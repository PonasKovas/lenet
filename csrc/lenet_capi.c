/*
 * Lenet C API implementation.
 *
 * This file is the ONLY place in the library where the Lean runtime is
 * visible. It wraps the raw Lean FFI exports (Lenet/FFI.lean, symbols
 * lenet_ffi_*) into the plain C API declared in ../include/lenet.h:
 *
 *   - lazy, idempotent Lean runtime bootstrap (pthread_once),
 *   - Lean reference-counting discipline (exported Lean functions take
 *     owned references; the host handle is incremented around every call
 *     and consumed by lenet_host_destroy),
 *   - IO result (EStateM) unwrapping,
 *   - ByteArray <-> (ptr, len) marshalling.
 *
 * Everything above this file — C or Rust — links against the built
 * library and sees only ../include/lenet.h.
 */
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <time.h>

#include <lean/lean.h>

#include "../include/lenet.h"

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
extern lean_object *lenet_ffi_peer_throttle_configure(lean_object *, uint16_t,
                                                      uint32_t, uint32_t, uint32_t);
extern lean_object *lenet_ffi_set_peer_timeout(lean_object *, uint16_t, uint32_t,
                                               uint32_t, uint32_t);
extern lean_object *lenet_ffi_host_handle_datagram(lean_object *, uint32_t,
                                                   uint32_t, uint16_t, lean_object *);
extern lean_object *lenet_ffi_host_service(lean_object *, uint32_t);
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

void lenet_initialize(void) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, lenet_bootstrap);
}

static void ensure_init(void) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, lenet_bootstrap);
}

/* ---- helpers ---- */

/* Extracts the ok-value of an exported `IO a` result, or aborts after
 * printing the error. Returns the value with +1 ref (caller must dec). */
static lean_object *ffi_value(lean_object *r) {
    if (!lean_io_result_is_ok(r)) {
        lean_io_result_show_error(r);
        lean_dec(r);
        fprintf(stderr, "lenet: FATAL: internal call failed\n");
        abort();
    }
    lean_object *v = lean_ctor_get(r, 0);
    lean_inc(v);
    lean_dec(r);
    return v;
}

/* 0 on ok, -1 on error; always releases r. */
static int ffi_status(lean_object *r) {
    int v = lean_io_result_is_ok(r) ? 0 : -1;
    lean_dec(r);
    return v;
}

/* Builds a Lean ByteArray from (data, len). */
static lean_object *mk_byte_array(const void *data, size_t len) {
    lean_object *arr = lean_mk_empty_byte_array(lean_box(len > 0 ? len : 1));
    const uint8_t *p = data;
    for (size_t i = 0; i < len; i++)
        arr = lean_byte_array_push(arr, p[i]);
    return arr;
}

/* ---- lifecycle ---- */

lenet_host *lenet_host_create(uint32_t bind_ip, uint16_t bind_port,
                              size_t peer_count, size_t channel_limit,
                              uint32_t incoming_bw, uint32_t outgoing_bw,
                              uint32_t mtu) {
    lenet_initialize();
    uint32_t seed = (uint32_t)time(NULL);
    if (mtu == 0) mtu = 1392;
    lean_object *r = lenet_ffi_host_create(bind_ip, bind_port, peer_count,
                                           channel_limit, incoming_bw,
                                           outgoing_bw, seed, mtu);
    if (!lean_io_result_is_ok(r)) {
        lean_io_result_show_error(r);
        lean_dec(r);
        return NULL;
    }
    lean_object *opt = lean_ctor_get(r, 0); /* Option (IO.Ref Ctx) */
    lean_inc(opt);
    lean_dec(r);
    if (lean_obj_tag(opt) != 1) { /* none */
        lean_dec(opt);
        return NULL;
    }
    lean_object *ref = lean_ctor_get(opt, 0);
    lean_inc(ref);
    lean_dec(opt);
    return (lenet_host *)ref; /* we hold the only reference */
}

void lenet_host_destroy(lenet_host *host) {
    if (host == NULL) return;
    /* the export consumes the handle's reference itself */
    lean_object *r = lenet_ffi_host_destroy((lean_object *)host);
    lean_dec(r);
}

/* ---- connection management ---- */

int32_t lenet_host_connect(lenet_host *host, uint32_t ip, uint16_t port,
                           size_t channel_count, uint32_t user_data) {
    if (host == NULL) return -1;
    ensure_init();
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_connect((lean_object *)host, ip, port,
                                            channel_count, user_data);
    int32_t v = -1;
    if (lean_io_result_is_ok(r))
        v = (int32_t)(uint32_t)lean_unbox(lean_ctor_get(r, 0));
    lean_dec(r);
    return v;
}

int32_t lenet_host_send(lenet_host *host, uint16_t peer_id, uint8_t channel,
                        uint32_t flags, const void *data, size_t len) {
    if (host == NULL) return -1;
    ensure_init();
    lean_object *arr = mk_byte_array(data, len);
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_send((lean_object *)host, peer_id, channel,
                                         flags, arr);
    int32_t v = lean_io_result_is_ok(r) ? 0 : -1;
    lean_dec(r);
    return v;
}

void lenet_host_broadcast(lenet_host *host, uint8_t channel, uint32_t flags,
                          const void *data, size_t len) {
    if (host == NULL) return;
    ensure_init();
    lean_object *arr = mk_byte_array(data, len);
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_broadcast((lean_object *)host, channel,
                                              flags, arr);
    lean_dec(r);
}

void lenet_host_disconnect(lenet_host *host, uint16_t peer_id, uint32_t data) {
    if (host == NULL) return;
    ensure_init();
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_disconnect((lean_object *)host, peer_id, data);
    lean_dec(r);
}

void lenet_host_disconnect_later(lenet_host *host, uint16_t peer_id, uint32_t data) {
    if (host == NULL) return;
    ensure_init();
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_disconnect_later((lean_object *)host, peer_id, data);
    lean_dec(r);
}

void lenet_host_enable_checksum(lenet_host *host) {
    if (host == NULL) return;
    ensure_init();
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_enable_checksum((lean_object *)host);
    lean_dec(r);
}

void lenet_peer_throttle_configure(lenet_host *host, uint16_t peer_id,
                                   uint32_t interval, uint32_t acceleration,
                                   uint32_t deceleration) {
    if (host == NULL) return;
    ensure_init();
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_peer_throttle_configure((lean_object *)host, peer_id,
                                                       interval, acceleration, deceleration);
    lean_dec(r);
}

void lenet_peer_set_timeout(lenet_host *host, uint16_t peer_id,
                            uint32_t limit, uint32_t minimum, uint32_t maximum) {
    if (host == NULL) return;
    ensure_init();
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_set_peer_timeout((lean_object *)host, peer_id,
                                                limit, minimum, maximum);
    lean_dec(r);
}

/* ---- sans-I/O ingest & service ---- */

int32_t lenet_host_handle_datagram(lenet_host *host, uint32_t now_ms,
                                   uint32_t ip, uint16_t port,
                                   const void *data, size_t len) {
    if (host == NULL) return -1;
    ensure_init();
    lean_object *arr = mk_byte_array(data, len);
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_handle_datagram((lean_object *)host, now_ms,
                                                    ip, port, arr);
    int32_t v = lean_io_result_is_ok(r) ? 0 : -1;
    lean_dec(r);
    return v;
}

int32_t lenet_host_service(lenet_host *host, uint32_t now_ms) {
    if (host == NULL) return -1;
    ensure_init();
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_service((lean_object *)host, now_ms);
    int32_t v = lean_io_result_is_ok(r) ? 0 : -1;
    lean_dec(r);
    return v;
}

/* ---- output polling ---- */

/* The outgoing datagram is copied into a thread-local buffer so that
 * hosts on different threads never share it. */
static _Thread_local uint8_t g_out_buf[64 * 1024];

int32_t lenet_host_poll_outgoing(lenet_host *host, lenet_datagram *out) {
    if (host == NULL || out == NULL) return -1;
    ensure_init();
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_poll_outgoing((lean_object *)host);

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
            size_t len = lean_sarray_size(arr);
            if (len > sizeof g_out_buf) len = sizeof g_out_buf;
            memcpy(g_out_buf, lean_sarray_cptr(arr), len);
            lean_dec(opt); /* frees the pair tree + array */
            out->ip = ip;
            out->port = (uint16_t)port;
            out->data = g_out_buf;
            out->len = len;
            ret = 1;
        }
    }
    return ret;
}

int32_t lenet_host_poll_event(lenet_host *host, lenet_event *out,
                              void *payload_buf, size_t payload_cap,
                              size_t *payload_len) {
    if (host == NULL || out == NULL) return -1;
    ensure_init();
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_poll_event((lean_object *)host);

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
            /* some (type, (peer, (channel, (data, payload)))):
             * right-nested product, 64-bit scalars unboxed from the
             * pointer bits */
            lean_object *p1 = lean_ctor_get(opt, 0);
            lean_object *p2 = lean_ctor_get(p1, 1);
            lean_object *p3 = lean_ctor_get(p2, 1);
            lean_object *p4 = lean_ctor_get(p3, 1);
            out->type = (uint32_t)lean_unbox_uint32(lean_ctor_get(p1, 0));
            out->peer_id = (uint16_t)lean_unbox(lean_ctor_get(p2, 0));
            out->channel_id = (uint8_t)lean_unbox(lean_ctor_get(p3, 0));
            out->data = (uint32_t)lean_unbox_uint32(lean_ctor_get(p4, 0));
            lean_object *arr = lean_ctor_get(p4, 1);
            size_t len = lean_sarray_size(arr);
            size_t copy = len < payload_cap ? len : payload_cap;
            if (payload_buf != NULL && copy > 0)
                memcpy(payload_buf, lean_sarray_cptr(arr), copy);
            if (payload_len != NULL)
                *payload_len = len;
            lean_dec(opt); /* frees the pair tree + array */
            ret = 1;
        }
    }
    return ret;
}
