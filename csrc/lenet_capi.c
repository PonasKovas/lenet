/*
 * Lenet C API implementation.
 *
 * This file is the ONLY place in the library where the Lean runtime is
 * visible. It wraps the raw Lean FFI exports (Lenet/FFI.lean, symbols
 * lenet_ffi_*) into the plain C API declared in include/lenet.h:
 *
 *   - lazy, idempotent Lean runtime bootstrap (pthread_once),
 *   - Lean reference-counting discipline (exported Lean functions take
 *     owned references; the host reference is incremented around every
 *     call (href) and consumed by lenet_host_destroy),
 *   - what each host keeps on the C side (struct lenet_host),
 *   - IO result (EStateM) unwrapping,
 *   - ByteArray <-> (ptr, len) marshalling.
 *
 * Everything above this file — C or Rust — links against the built
 * library and sees only include/lenet.h.
 */
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <sys/random.h>
#include <time.h>

#include <lean/lean.h>

#include "include/lenet.h"

/* ---- the handle ---- */

/* A host: the Lean host plus what the C side keeps for it. Pointers handed
 * out by lenet_host_poll_outgoing point into `out`, so they belong to this
 * host alone and stay valid until its next poll_outgoing or destroy. */
struct lenet_host {
    lean_object *ref;     /* IO.Ref HostContext, owned */
    lean_object *out;     /* ByteArray of the last polled datagram, or NULL */
    lean_object *pending; /* an event poll_event could not hand out whole, or NULL */
};

/* The Lean host with one more reference: the exports consume one. */
static lean_object *href(lenet_host *h) {
    lean_inc(h->ref);
    return h->ref;
}

/* ---- raw Lean FFI exports (implemented in Lenet/FFI.lean) ---- */

extern lean_object *lenet_ffi_host_create(uint32_t, uint16_t, size_t, size_t,
                                          uint32_t, uint32_t, uint32_t, uint32_t);
extern lean_object *lenet_ffi_host_destroy(lean_object *);
extern lean_object *lenet_ffi_host_connect(lean_object *, uint32_t, uint16_t,
                                           size_t, uint32_t);
extern lean_object *lenet_ffi_host_send(lean_object *, uint16_t, uint8_t,
                                        uint32_t, lean_object *);
extern lean_object *lenet_ffi_host_broadcast(lean_object *, uint8_t, uint32_t,
                                             lean_object *);
extern lean_object *lenet_ffi_host_disconnect(lean_object *, uint16_t, uint32_t);
extern lean_object *lenet_ffi_host_disconnect_later(lean_object *, uint16_t, uint32_t);
extern lean_object *lenet_ffi_host_enable_checksum(lean_object *);
extern lean_object *lenet_ffi_peer_disconnect_now(lean_object *, uint16_t, uint32_t);
extern lean_object *lenet_ffi_peer_reset(lean_object *, uint16_t);
extern lean_object *lenet_ffi_peer_ping(lean_object *, uint16_t);
extern lean_object *lenet_ffi_peer_ping_interval(lean_object *, uint16_t, uint32_t);
extern lean_object *lenet_ffi_host_bandwidth_limit(lean_object *, uint32_t, uint32_t);
extern lean_object *lenet_ffi_host_channel_limit(lean_object *, size_t);
extern lean_object *lenet_ffi_peer_info(lean_object *, uint16_t);
extern lean_object *lenet_ffi_host_flush(lean_object *, uint32_t);
extern lean_object *lenet_ffi_peer_throttle_configure(lean_object *, uint16_t,
                                                      uint32_t, uint32_t, uint32_t);
extern lean_object *lenet_ffi_set_peer_timeout(lean_object *, uint16_t, uint32_t,
                                               uint32_t, uint32_t);
extern lean_object *lenet_ffi_host_handle_datagram(lean_object *, uint32_t,
                                                   uint32_t, uint16_t, lean_object *);
extern lean_object *lenet_ffi_host_service(lean_object *, uint32_t);
extern lean_object *lenet_ffi_host_next_deadline(lean_object *);
extern lean_object *lenet_ffi_host_poll_event(lean_object *);
extern lean_object *lenet_ffi_host_poll_outgoing(lean_object *);

extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_lenet_Lenet(uint8_t builtin);

/* ---- Lean runtime bootstrap ---- */

static void lenet_bootstrap(void) {
    lean_initialize_runtime_module();
    lean_object *res = initialize_lenet_Lenet(1 /* builtin */);
    lean_io_mark_end_initialization();
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        fprintf(stderr, "lenet: FATAL: Lean runtime initialization failed\n");
        abort();
    }
    lean_dec_ref(res);
}

/* Every other entry point takes a host, and hosts only come from
 * lenet_host_create, which initializes: they need no check of their own. */
void lenet_initialize(void) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, lenet_bootstrap);
}

/* ---- helpers ---- */

/* 0 on ok, -1 on error; always releases r. */
static int ffi_status(lean_object *r) {
    int v = lean_io_result_is_ok(r) ? 0 : -1;
    lean_dec(r);
    return v;
}

/* Builds a Lean ByteArray from (data, len). */
static lean_object *mk_byte_array(const void *data, size_t len) {
    lean_object *arr = lean_alloc_sarray(1, len, len);
    if (len > 0)
        memcpy(lean_sarray_cptr(arr), data, len);
    return arr;
}

/* ---- lifecycle ---- */

/* The seed of a host's connect IDs: from the OS, or else the clock's
 * nanoseconds mixed with the host's address, so hosts made together still
 * differ (ENet mixes in the host pointer too). */
static uint32_t host_seed(const void *salt) {
    uint32_t seed;
    if (getrandom(&seed, sizeof seed, GRND_NONBLOCK) == (ssize_t)sizeof seed)
        return seed;
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint32_t)ts.tv_nsec ^ (uint32_t)ts.tv_sec * 2654435761u ^
        (uint32_t)(uintptr_t)salt;
}

lenet_host *lenet_host_create(uint32_t bind_ip, uint16_t bind_port,
                              size_t peer_count, size_t channel_limit,
                              uint32_t incoming_bw, uint32_t outgoing_bw,
                              uint32_t mtu) {
    lenet_initialize();
    /* peer ID 0xFFF addresses CONNECTs (ENet enet_host_create refuses too) */
    if (peer_count > 0xFFF) return NULL;
    lenet_host *h = malloc(sizeof *h);
    if (h == NULL) return NULL;
    uint32_t seed = host_seed(h);
    if (mtu == 0) mtu = 1392;
    lean_object *r = lenet_ffi_host_create(bind_ip, bind_port, peer_count,
                                           channel_limit, incoming_bw,
                                           outgoing_bw, seed, mtu);
    if (!lean_io_result_is_ok(r)) {
        lean_io_result_show_error(r);
        lean_dec(r);
        free(h);
        return NULL;
    }
    h->ref = lean_ctor_get(r, 0); /* IO.Ref HostContext */
    lean_inc(h->ref);
    lean_dec(r);
    h->out = NULL;
    h->pending = NULL;
    return h;
}

void lenet_host_destroy(lenet_host *host) {
    if (host == NULL) return;
    if (host->out != NULL) lean_dec(host->out);
    if (host->pending != NULL) lean_dec(host->pending);
    /* the export consumes the host's reference itself */
    lean_object *r = lenet_ffi_host_destroy(host->ref);
    lean_dec(r);
    free(host);
}

/* ---- connection management ---- */

int32_t lenet_host_connect(lenet_host *host, uint32_t ip, uint16_t port,
                           size_t channel_count, uint32_t user_data) {
    if (host == NULL) return -1;
    lean_object *r = lenet_ffi_host_connect(href(host), ip, port,
                                            channel_count, user_data);
    int32_t v = -1;
    if (lean_io_result_is_ok(r))
        v = (int32_t)(uint32_t)lean_unbox(lean_ctor_get(r, 0));
    lean_dec(r);
    return v;
}

int32_t lenet_host_send(lenet_host *host, uint16_t peer_id, uint8_t channel,
                        uint32_t flags, const void *data, size_t len) {
    if (host == NULL || len > LENET_MAX_PACKET_SIZE) return -1;
    lean_object *arr = mk_byte_array(data, len);
    lean_object *r = lenet_ffi_host_send(href(host), peer_id, channel,
                                         flags, arr);
    /* the export reports a rejected send as -1 inside a successful IO */
    int32_t v = lean_io_result_is_ok(r)
        ? (int32_t)lean_unbox_uint32(lean_ctor_get(r, 0)) : -1;
    lean_dec(r);
    return v;
}

void lenet_host_broadcast(lenet_host *host, uint8_t channel, uint32_t flags,
                          const void *data, size_t len) {
    if (host == NULL || len > LENET_MAX_PACKET_SIZE) return;
    lean_object *arr = mk_byte_array(data, len);
    lean_object *r = lenet_ffi_host_broadcast(href(host), channel,
                                              flags, arr);
    lean_dec(r);
}

void lenet_host_disconnect(lenet_host *host, uint16_t peer_id, uint32_t data) {
    if (host == NULL) return;
    lean_object *r = lenet_ffi_host_disconnect(href(host), peer_id, data);
    lean_dec(r);
}

void lenet_host_disconnect_later(lenet_host *host, uint16_t peer_id, uint32_t data) {
    if (host == NULL) return;
    lean_object *r = lenet_ffi_host_disconnect_later(href(host), peer_id, data);
    lean_dec(r);
}

void lenet_peer_disconnect_now(lenet_host *host, uint16_t peer_id, uint32_t data) {
    if (host == NULL) return;
    lean_dec(lenet_ffi_peer_disconnect_now(href(host), peer_id, data));
}

void lenet_peer_reset(lenet_host *host, uint16_t peer_id) {
    if (host == NULL) return;
    lean_dec(lenet_ffi_peer_reset(href(host), peer_id));
}

void lenet_peer_ping(lenet_host *host, uint16_t peer_id) {
    if (host == NULL) return;
    lean_dec(lenet_ffi_peer_ping(href(host), peer_id));
}

void lenet_peer_ping_interval(lenet_host *host, uint16_t peer_id, uint32_t interval_ms) {
    if (host == NULL) return;
    lean_dec(lenet_ffi_peer_ping_interval(href(host), peer_id, interval_ms));
}

void lenet_host_bandwidth_limit(lenet_host *host, uint32_t incoming_bw, uint32_t outgoing_bw) {
    if (host == NULL) return;
    lean_dec(lenet_ffi_host_bandwidth_limit(href(host), incoming_bw, outgoing_bw));
}

void lenet_host_channel_limit(lenet_host *host, size_t channel_limit) {
    if (host == NULL) return;
    lean_dec(lenet_ffi_host_channel_limit(href(host), channel_limit));
}

int32_t lenet_peer_get_info(lenet_host *host, uint16_t peer_id, lenet_peer_info *out) {
    if (host == NULL || out == NULL) return -1;
    lean_object *r = lenet_ffi_peer_info(href(host), peer_id);
    if (!lean_io_result_is_ok(r)) {
        lean_dec(r);
        return -1;
    }
    lean_object *opt = lean_ctor_get(r, 0); /* Option value */
    lean_inc(opt);
    lean_dec(r);
    if (lean_obj_tag(opt) == 0) { /* none: no such peer */
        lean_dec(opt);
        return -1;
    }
    /* some (state, (ip, (port, (rtt, (variance, throttle))))) */
    lean_object *p1 = lean_ctor_get(opt, 0);
    lean_object *p2 = lean_ctor_get(p1, 1);
    lean_object *p3 = lean_ctor_get(p2, 1);
    lean_object *p4 = lean_ctor_get(p3, 1);
    lean_object *p5 = lean_ctor_get(p4, 1);
    out->state = (uint32_t)lean_unbox_uint32(lean_ctor_get(p1, 0));
    out->ip = (uint32_t)lean_unbox_uint32(lean_ctor_get(p2, 0));
    out->port = (uint16_t)lean_unbox(lean_ctor_get(p3, 0));
    out->round_trip_time = (uint32_t)lean_unbox_uint32(lean_ctor_get(p4, 0));
    out->round_trip_time_variance = (uint32_t)lean_unbox_uint32(lean_ctor_get(p5, 0));
    out->packet_throttle = (uint32_t)lean_unbox_uint32(lean_ctor_get(p5, 1));
    lean_dec(opt);
    return 0;
}

void lenet_host_enable_checksum(lenet_host *host) {
    if (host == NULL) return;
    lean_object *r = lenet_ffi_host_enable_checksum(href(host));
    lean_dec(r);
}

void lenet_peer_throttle_configure(lenet_host *host, uint16_t peer_id,
                                   uint32_t interval, uint32_t acceleration,
                                   uint32_t deceleration) {
    if (host == NULL) return;
    lean_object *r = lenet_ffi_peer_throttle_configure(href(host), peer_id,
                                                       interval, acceleration, deceleration);
    lean_dec(r);
}

void lenet_peer_set_timeout(lenet_host *host, uint16_t peer_id,
                            uint32_t limit, uint32_t minimum, uint32_t maximum) {
    if (host == NULL) return;
    lean_object *r = lenet_ffi_set_peer_timeout(href(host), peer_id,
                                                limit, minimum, maximum);
    lean_dec(r);
}

/* ---- sans-I/O ingest & service ---- */

int32_t lenet_host_handle_datagram(lenet_host *host, uint32_t now_ms,
                                   uint32_t ip, uint16_t port,
                                   const void *data, size_t len) {
    if (host == NULL || len > 65535) return -1;
    lean_object *arr = mk_byte_array(data, len);
    return ffi_status(lenet_ffi_host_handle_datagram(href(host), now_ms,
                                                     ip, port, arr));
}

int32_t lenet_host_flush(lenet_host *host, uint32_t now_ms) {
    if (host == NULL) return -1;
    return ffi_status(lenet_ffi_host_flush(href(host), now_ms));
}

int32_t lenet_host_service(lenet_host *host, uint32_t now_ms) {
    if (host == NULL) return -1;
    return ffi_status(lenet_ffi_host_service(href(host), now_ms));
}

/* ---- output polling ---- */

int32_t lenet_host_next_deadline(lenet_host *host, uint32_t *deadline) {
    if (host == NULL || deadline == NULL) return -1;
    lean_object *r = lenet_ffi_host_next_deadline(href(host));
    if (!lean_io_result_is_ok(r)) {
        lean_dec(r);
        return -1;
    }
    lean_object *opt = lean_ctor_get(r, 0); /* Option UInt32 */
    lean_inc(opt);
    lean_dec(r);
    if (lean_obj_tag(opt) == 0) { /* none */
        lean_dec(opt);
        return 0;
    }
    *deadline = (uint32_t)lean_unbox_uint32(lean_ctor_get(opt, 0));
    lean_dec(opt);
    return 1;
}

int32_t lenet_host_poll_outgoing(lenet_host *host, lenet_datagram *out) {
    if (host == NULL || out == NULL) return -1;
    lean_object *r = lenet_ffi_host_poll_outgoing(href(host));

    int32_t ret;
    if (!lean_io_result_is_ok(r)) {
        ret = -1;
        lean_dec(r);
    } else {
        lean_object *opt = lean_ctor_get(r, 0); /* Option value */
        lean_inc(opt);
        lean_dec(r);
        if (lean_obj_tag(opt) == 0) { /* none */
            lean_dec(opt);
            ret = 0;
        } else {
            /* some (ip, (port, bytes)): right-nested product, 64-bit
             * scalars are unboxed pointer values */
            lean_object *p1 = lean_ctor_get(opt, 0);
            lean_object *p2 = lean_ctor_get(p1, 1);
            uint32_t ip = (uint32_t)lean_unbox_uint32(lean_ctor_get(p1, 0));
            uint32_t port = (uint32_t)lean_unbox(lean_ctor_get(p2, 0));
            lean_object *arr = lean_ctor_get(p2, 1);
            /* the host keeps the bytes until its next poll: no copy */
            lean_inc(arr);
            lean_dec(opt); /* frees the pair tree */
            if (host->out != NULL) lean_dec(host->out);
            host->out = arr;
            out->ip = ip;
            out->port = (uint16_t)port;
            out->data = lean_sarray_cptr(arr);
            out->len = lean_sarray_size(arr);
            ret = 1;
        }
    }
    return ret;
}

int32_t lenet_host_poll_event(lenet_host *host, lenet_event *out,
                              void *payload_buf, size_t payload_cap,
                              size_t *payload_len) {
    if (host == NULL || out == NULL) return -1;
    lean_object *opt; /* some event */
    if (host->pending != NULL) {
        opt = host->pending;
        host->pending = NULL;
    } else {
        lean_object *r = lenet_ffi_host_poll_event(href(host));
        if (!lean_io_result_is_ok(r)) {
            lean_dec(r);
            return -1;
        }
        opt = lean_ctor_get(r, 0); /* Option value */
        lean_inc(opt);
        lean_dec(r);
        if (lean_obj_tag(opt) == 0) { /* none */
            lean_dec(opt);
            return 0;
        }
    }
    /* some (type, (peer, (channel, (data, payload)))): right-nested
     * product, 64-bit scalars unboxed from the pointer bits */
    lean_object *p1 = lean_ctor_get(opt, 0);
    lean_object *p2 = lean_ctor_get(p1, 1);
    lean_object *p3 = lean_ctor_get(p2, 1);
    lean_object *p4 = lean_ctor_get(p3, 1);
    lean_object *arr = lean_ctor_get(p4, 1);
    size_t len = lean_sarray_size(arr);
    if (payload_len != NULL)
        *payload_len = len;
    if (len > 0 && (payload_buf == NULL || payload_cap < len)) {
        /* does not fit: keep the event for the next call */
        host->pending = opt;
        return -2;
    }
    out->type = (uint32_t)lean_unbox_uint32(lean_ctor_get(p1, 0));
    out->peer_id = (uint16_t)lean_unbox(lean_ctor_get(p2, 0));
    out->channel_id = (uint8_t)lean_unbox(lean_ctor_get(p3, 0));
    out->data = (uint32_t)lean_unbox_uint32(lean_ctor_get(p4, 0));
    if (len > 0)
        memcpy(payload_buf, lean_sarray_cptr(arr), len);
    lean_dec(opt); /* frees the pair tree + array */
    return 1;
}
