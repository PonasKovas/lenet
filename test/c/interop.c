/*
 * Live interop harness: a real C ENet host and a Lenet sans-I/O host
 * (driven through the Lean FFI) talk to each other over actual UDP
 * sockets in one process.
 *
 * Usage: interop <scenario>
 *   connect       lenet client -> C server handshake + one packet each way
 *   connect_r     C client -> lenet server handshake
 *   send          reliable/unreliable/unsequenced, both directions
 *   frag          40000-byte fragmented reliable send, both directions
 *   disconnect    lenet-initiated graceful disconnect
 *   disconnect_r  C-initiated graceful disconnect
 *   timeout       lenet stops responding -> C peer timeout
 *
 * Exit code 0 = scenario passed.
 *
 * The Lenet side is exercised through the public C API declared in
 * ../../include/lenet.h, implemented here as a shim over the raw Lean
 * exports from Lenet/FFI.lean (lenet_ffi_*). Every export returns an
 * EStateM result object: tag 0 = ok (field 0 = value), tag 1 = error.
 */
#include <enet/enet.h>
#include <lean/lean.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>
#include <fcntl.h>
#include <sys/socket.h>
#include <netinet/in.h>

#include "../../include/lenet.h"

/* ---- raw Lean FFI exports (Lenet/FFI.lean) ---- */

extern lean_object *lenet_ffi_host_create(uint32_t, uint16_t, size_t, size_t,
                                          uint32_t, uint32_t, uint32_t);
extern lean_object *lenet_ffi_host_destroy(lean_object *);
extern lean_object *lenet_ffi_host_connect(lean_object *, uint32_t, uint16_t,
                                           size_t, uint32_t);
extern lean_object *lenet_ffi_host_send(lean_object *, uint16_t, uint8_t,
                                        uint32_t, lean_object *);
extern lean_object *lenet_ffi_host_broadcast(lean_object *, uint8_t, uint32_t,
                                             lean_object *);
extern lean_object *lenet_ffi_host_disconnect(lean_object *, uint16_t, uint32_t);
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

static void lenet_ffi_initialize(void) {
    lean_initialize_runtime_module();
    lean_object *res = initialize_lenet_Lenet(1 /* builtin */);
    lean_io_mark_end_initialization();
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        exit(2);
    }
    lean_dec_ref(res);
}

/* Extract the value of a successful export result (or die showing it). */
static b_lean_obj_res ffi_result_value(lean_object *r) {
    if (!lean_io_result_is_ok(r)) {
        lean_io_result_show_error(r);
        lean_dec(r);
        fprintf(stderr, "FATAL: lean FFI call failed\n");
        exit(2);
    }
    b_lean_obj_res v = lean_io_result_get_value(r);
    lean_inc(v);
    lean_dec(r);
    return v;
}

/* ---- public lenet.h API over the raw exports ----
 * Event/outgoing packet buffers stay valid until the next poll call. */

static uint8_t g_event_buf[1024 * 1024];
static uint8_t g_out_buf[64 * 1024];

LeNetHost *lenet_host_create(uint32_t host_ip, uint16_t port, size_t peer_count,
                             size_t channel_limit, uint32_t in_bw, uint32_t out_bw,
                             uint32_t seed) {
    lean_object *opt = ffi_result_value(
        lenet_ffi_host_create(host_ip, port, peer_count, channel_limit,
                              in_bw, out_bw, seed));
    lean_object *ref = NULL;
    if (lean_obj_tag(opt) == 1) { /* some */
        ref = lean_ctor_get(opt, 0);
        lean_inc(ref);
    }
    lean_dec(opt);
    if (ref == NULL) { fprintf(stderr, "FATAL: host_create returned none\n"); exit(2); }
    return (LeNetHost *)ref;
}

void lenet_host_destroy(LeNetHost *host) {
    /* the export consumes the context ref itself */
    lean_dec(lenet_ffi_host_destroy((lean_object *)host));
}

static lean_object *mk_byte_array(const uint8_t *data, size_t len) {
    lean_object *arr = lean_mk_empty_byte_array(lean_box(len > 0 ? len : 1));
    for (size_t i = 0; i < len; i++)
        arr = lean_byte_array_push(arr, data[i]);
    return arr;
}

int32_t lenet_host_connect(LeNetHost *host, uint32_t ip, uint16_t port,
                           size_t channels, uint32_t data) {
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_connect((lean_object *)host, ip, port,
                                            channels, data);
    int32_t v = -1;
    if (lean_io_result_is_ok(r))
        v = (int32_t)(uint32_t)lean_unbox(lean_ctor_get(r, 0));
    lean_dec(r);
    return v;
}

int32_t lenet_host_send(LeNetHost *host, uint16_t peer_id, uint8_t channel,
                        uint32_t mode, const uint8_t *data, size_t len) {
    lean_object *arr = mk_byte_array(data, len);
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_send((lean_object *)host, peer_id, channel,
                                         mode, arr);
    int32_t v = lean_io_result_is_ok(r) ? 0 : -1;
    lean_dec(r);
    return v;
}

void lenet_host_broadcast(LeNetHost *host, uint8_t channel, uint32_t mode,
                          const uint8_t *data, size_t len) {
    lean_object *arr = mk_byte_array(data, len);
    lean_inc((lean_object *)host);
    lean_dec(lenet_ffi_host_broadcast((lean_object *)host, channel, mode, arr));
}

void lenet_host_disconnect(LeNetHost *host, uint16_t peer_id, uint32_t data) {
    lean_inc((lean_object *)host);
    lean_dec(lenet_ffi_host_disconnect((lean_object *)host, peer_id, data));
}

void lenet_peer_set_timeout(LeNetHost *host, uint16_t peer_id,
                            uint32_t limit, uint32_t minimum, uint32_t maximum) {
    lean_inc((lean_object *)host);
    lean_dec(lenet_ffi_set_peer_timeout((lean_object *)host, peer_id,
                                        limit, minimum, maximum));
}

int32_t lenet_host_handle_datagram(LeNetHost *host, uint32_t now, uint32_t ip,
                                   uint16_t port, const uint8_t *data, size_t len) {
    lean_object *arr = mk_byte_array(data, len);
    lean_inc((lean_object *)host);
    lean_object *r =
        lenet_ffi_host_handle_datagram((lean_object *)host, now, ip, port, arr);
    int32_t v = lean_io_result_is_ok(r) ? 0 : -1;
    lean_dec(r);
    return v;
}

int32_t lenet_host_service(LeNetHost *host, uint32_t now) {
    lean_inc((lean_object *)host);
    lean_object *r = lenet_ffi_host_service((lean_object *)host, now);
    int32_t v = lean_io_result_is_ok(r) ? 0 : -1;
    lean_dec(r);
    return v;
}

int32_t lenet_host_poll_event(LeNetHost *host, LeNetEvent *ev) {
    lean_inc((lean_object *)host);
    lean_object *opt = ffi_result_value(lenet_ffi_host_poll_event((lean_object *)host));
    if (lean_obj_tag(opt) == 0) { /* none */
        lean_dec(opt);
        return 0;
    }
    /* tuple is right-nested PProd: (type, (peer, (chan, (data, arr)))) */
    lean_object *n1 = lean_ctor_get(opt, 0);
    lean_object *n2 = lean_ctor_get(n1, 1);
    lean_object *n3 = lean_ctor_get(n2, 1);
    lean_object *n4 = lean_ctor_get(n3, 1);
    uint32_t type = lean_unbox_uint32(lean_ctor_get(n1, 0));
    uint32_t peer = lean_unbox_uint32(lean_ctor_get(n2, 0));
    uint32_t chan = lean_unbox_uint32(lean_ctor_get(n3, 0));
    uint32_t data = lean_unbox_uint32(lean_ctor_get(n4, 0));
    lean_object *arr = lean_ctor_get(n4, 1);
    size_t len = lean_sarray_size(arr);
    if (len > sizeof g_event_buf) len = sizeof g_event_buf;
    memcpy(g_event_buf, lean_sarray_cptr(arr), len);
    lean_dec(opt); /* frees the whole tree */
    ev->type = (LeNetEventType)type;
    ev->peer_id = (uint16_t)peer;
    ev->channel_id = (uint8_t)chan;
    ev->data = data;
    ev->packet_data = g_event_buf;
    ev->packet_len = len;
    return 1;
}

int32_t lenet_host_poll_outgoing(LeNetHost *host, LeNetOutgoingPacket *out) {
    lean_inc((lean_object *)host);
    lean_object *opt = ffi_result_value(lenet_ffi_host_poll_outgoing((lean_object *)host));
    if (lean_obj_tag(opt) == 0) { /* none */
        lean_dec(opt);
        return 0;
    }
    /* tuple is right-nested PProd: (ip, (port, arr)) */
    lean_object *n1 = lean_ctor_get(opt, 0);
    lean_object *n2 = lean_ctor_get(n1, 1);
    uint32_t ip = lean_unbox_uint32(lean_ctor_get(n1, 0));
    uint32_t port = lean_unbox_uint32(lean_ctor_get(n2, 0));
    lean_object *arr = lean_ctor_get(n2, 1);
    size_t len = lean_sarray_size(arr);
    if (len > sizeof g_out_buf) len = sizeof g_out_buf;
    memcpy(g_out_buf, lean_sarray_cptr(arr), len);
    lean_dec(opt); /* frees the whole tree */
    out->dest_ip = ip;
    out->dest_port = (uint16_t)port;
    out->data = g_out_buf;
    out->data_len = len;
    return 1;
}

/* ---- live harness ---- */

#define LENET_PORT 40010
#define ENET_PORT  40011

static ENetHost *g_enet;
static ENetPeer *g_enet_peer;
static int g_lenet_fd = -1;
static int32_t g_lenet_peer = -1;
static LeNetHost *g_lenet;

static int g_l_connected, g_c_connected, g_l_disconnected, g_c_disconnected;
static int g_lenet_dead;            /* stop servicing lenet (timeout scenario) */
static int g_l_connect_data = -1;   /* data from lenet's CONNECT event */
static int g_c_connect_data = -1;   /* data from enet's CONNECT event */
static int g_l_disc_data = -1;      /* data from lenet's DISCONNECT event */
static int g_c_disc_data = -1;      /* data from enet's DISCONNECT event */
static int g_l_pkts, g_c_pkts;      /* packets received on each side */
static uint8_t g_l_ch0[64 * 1024], g_c_ch0[64 * 1024];
static uint8_t g_l_ch1[4096], g_c_ch1[4096];
static size_t g_l_ch0len, g_c_ch0len, g_l_ch1len, g_c_ch1len;
static uint32_t g_start;

#define CHECK(cond, ...) do { \
    if (!(cond)) { fprintf(stderr, "FAIL: " __VA_ARGS__); \
                   fprintf(stderr, "\n  at %s:%d\n", __func__, __LINE__); return -1; } } while (0)

/* Pump until COND holds or MS milliseconds elapse. */
#define WAIT(COND, MS, ...) do { \
    g_start = now_ms(); \
    while (!(COND)) { \
        if (timed_out(MS)) CHECK(0, __VA_ARGS__); \
        pump(); usleep(500); \
    } } while (0)

static uint32_t now_ms(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint32_t)(t.tv_sec * 1000 + t.tv_nsec / 1000000);
}

static int timed_out(int ms) { return (int)(now_ms() - g_start) > ms; }

static ENetHost *create_enet_host(uint32_t host, uint16_t port, size_t peers) {
    ENetAddress a;
    memset(&a, 0, sizeof a);
    a.host = host;
    a.port = port;
    ENetHost *h = enet_host_create(&a, peers, 2, 0, 0);
    if (!h) { fprintf(stderr, "FATAL: enet_host_create\n"); exit(2); }
    return h;
}

static int make_udp(uint16_t port) {
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) { perror("socket"); exit(2); }
    struct sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    a.sin_port = htons(port);
    if (bind(fd, (struct sockaddr *)&a, sizeof a) < 0) { perror("bind"); exit(2); }
    int fl = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, fl | O_NONBLOCK);
    return fd;
}

/* One pump iteration: feed lenet, run enet, emit lenet's outputs. */
static void pump(void) {
    static uint8_t buf[64 * 1024];

    /* 1. incoming datagrams -> lenet, then periodic service */
    if (!g_lenet_dead && g_lenet) {
        for (;;) {
            struct sockaddr_in from;
            socklen_t flen = sizeof from;
            ssize_t n = recvfrom(g_lenet_fd, buf, sizeof buf, 0,
                                 (struct sockaddr *)&from, &flen);
            if (n < 0) break;
            lenet_host_handle_datagram(g_lenet, now_ms(),
                                       from.sin_addr.s_addr, ntohs(from.sin_port),
                                       buf, (size_t)n);
        }
        lenet_host_service(g_lenet, now_ms());
    }

    /* 2. enet host events */
    ENetEvent ev;
    while (enet_host_service(g_enet, &ev, 0) > 0) {
        switch (ev.type) {
        case ENET_EVENT_TYPE_CONNECT:
            g_enet_peer = ev.peer;
            g_c_connected = 1;
            g_c_connect_data = (int)ev.data;
            printf("  enet: CONNECT data=%u\n", ev.data);
            break;
        case ENET_EVENT_TYPE_RECEIVE:
            printf("  enet: RECEIVE ch=%u len=%u\n", ev.channelID, ev.packet->dataLength);
            if (ev.channelID == 0 && g_c_ch0len + ev.packet->dataLength <= sizeof g_c_ch0) {
                memcpy(g_c_ch0 + g_c_ch0len, ev.packet->data, ev.packet->dataLength);
                g_c_ch0len += ev.packet->dataLength;
            } else if (ev.channelID == 1 && g_c_ch1len + ev.packet->dataLength <= sizeof g_c_ch1) {
                memcpy(g_c_ch1 + g_c_ch1len, ev.packet->data, ev.packet->dataLength);
                g_c_ch1len += ev.packet->dataLength;
            }
            g_c_pkts++;
            enet_packet_destroy(ev.packet);
            break;
        case ENET_EVENT_TYPE_DISCONNECT:
            g_c_disconnected = 1;
            g_c_disc_data = (int)ev.data;
            printf("  enet: DISCONNECT data=%u\n", ev.data);
            break;
        default:
            break;
        }
    }

    /* 3. lenet outputs: send datagrams, collect events */
    if (!g_lenet_dead && g_lenet) {
        LeNetOutgoingPacket out;
        while (lenet_host_poll_outgoing(g_lenet, &out) == 1) {
            struct sockaddr_in a;
            memset(&a, 0, sizeof a);
            a.sin_family = AF_INET;
            a.sin_addr.s_addr = out.dest_ip;
            a.sin_port = htons(out.dest_port);
            sendto(g_lenet_fd, out.data, out.data_len, 0,
                   (struct sockaddr *)&a, sizeof a);
        }
        LeNetEvent lev;
        while (lenet_host_poll_event(g_lenet, &lev) == 1) {
            switch (lev.type) {
            case LENET_EVENT_TYPE_CONNECT:
                g_l_connected = 1;
                g_l_connect_data = (int)lev.data;
                printf("  lenet: CONNECT peer=%u data=%u\n", lev.peer_id, lev.data);
                break;
            case LENET_EVENT_TYPE_DISCONNECT:
                g_l_disconnected = 1;
                g_l_disc_data = (int)lev.data;
                printf("  lenet: DISCONNECT peer=%u data=%u\n", lev.peer_id, lev.data);
                break;
            case LENET_EVENT_TYPE_RECEIVE:
                printf("  lenet: RECEIVE ch=%u len=%zu\n", lev.channel_id, lev.packet_len);
                if (lev.channel_id == 0 && g_l_ch0len + lev.packet_len <= sizeof g_l_ch0) {
                    memcpy(g_l_ch0 + g_l_ch0len, lev.packet_data, lev.packet_len);
                    g_l_ch0len += lev.packet_len;
                    g_l_pkts++;
                } else if (lev.channel_id == 1 && g_l_ch1len + lev.packet_len <= sizeof g_l_ch1) {
                    memcpy(g_l_ch1 + g_l_ch1len, lev.packet_data, lev.packet_len);
                    g_l_ch1len += lev.packet_len;
                    g_l_pkts++;
                }
                break;
            default:
                break;
            }
        }
    }
}

/* lenet-as-client, connected to the C server */
static int setup_client_connected(uint32_t connect_data) {
    fprintf(stderr, "CHECKPOINT: create_enet_host\n");
    g_enet = create_enet_host(htonl(INADDR_LOOPBACK), ENET_PORT, 16);
    fprintf(stderr, "CHECKPOINT: enet host ok\n");
    g_lenet_fd = make_udp(LENET_PORT);
    fprintf(stderr, "CHECKPOINT: lenet create\n");
    g_lenet = lenet_host_create(htonl(INADDR_LOOPBACK), LENET_PORT, 1, 2, 0, 0, 1234);
    fprintf(stderr, "CHECKPOINT: lenet host ok\n");
    fprintf(stderr, "CHECKPOINT: connecting\n");
    g_lenet_peer = lenet_host_connect(g_lenet, htonl(INADDR_LOOPBACK), ENET_PORT,
                                      2, connect_data);
    CHECK(g_lenet_peer >= 0, "lenet_host_connect failed");
    WAIT(g_l_connected && g_c_connected, 2000,
         "handshake timeout (l=%d c=%d)", g_l_connected, g_c_connected);
    return 0;
}

/* lenet-as-server, C client connects to it */
static int setup_server_connected(uint32_t connect_data) {
    g_enet = create_enet_host(htonl(INADDR_LOOPBACK), ENET_PORT, 1);
    g_lenet_fd = make_udp(LENET_PORT);
    g_lenet = lenet_host_create(htonl(INADDR_LOOPBACK), LENET_PORT, 16, 2, 0, 0, 1234);
    ENetAddress taddr;
    memset(&taddr, 0, sizeof taddr);
    taddr.host = htonl(INADDR_LOOPBACK);
    taddr.port = LENET_PORT;
    g_enet_peer = enet_host_connect(g_enet, &taddr, 2, connect_data);
    CHECK(g_enet_peer != NULL, "enet_host_connect failed");
    WAIT(g_l_connected && g_c_connected, 2000,
         "reverse handshake timeout (l=%d c=%d)", g_l_connected, g_c_connected);
    return 0;
}

static int scen_connect(void) {
    CHECK(setup_client_connected(0x77) == 0, "setup failed");
    CHECK(g_l_connect_data == 0x77, "lenet CONNECT data=%d, want 0x77", g_l_connect_data);
    CHECK(g_c_connect_data == 0x77, "enet CONNECT data=%d, want 0x77", g_c_connect_data);

    const char *to_c = "ping-from-lenet";
    CHECK(lenet_host_send(g_lenet, (uint16_t)g_lenet_peer, 0,
                          LENET_DELIVERY_RELIABLE, (const uint8_t *)to_c, 15) == 0,
          "lenet send failed");
    WAIT(g_c_pkts >= 1, 2000, "packet lenet->C did not arrive");
    CHECK(g_c_ch0len == 15 && memcmp(g_c_ch0, "ping-from-lenet", 15) == 0,
          "enet received wrong bytes");

    const char *from_c = "ping-from-enet";
    ENetPacket *pkt = enet_packet_create(from_c, 14, ENET_PACKET_FLAG_RELIABLE);
    enet_peer_send(g_enet_peer, 0, pkt);
    WAIT(g_l_ch0len >= 14, 2000, "lenet did not receive packet");
    CHECK(g_l_ch0len == 14 && memcmp(g_l_ch0, from_c, 14) == 0,
          "lenet received wrong bytes");
    return 0;
}

static int scen_connect_r(void) {
    CHECK(setup_server_connected(0x99) == 0, "setup failed");
    /* lenet (server) surfaces the client's connect data in its CONNECT event;
     * ENet's client-side CONNECT event data is peer->eventData, which stays 0. */
    CHECK(g_l_connect_data == 0x99, "lenet CONNECT data=%d, want 0x99", g_l_connect_data);
    CHECK(g_c_connect_data == 0, "enet CONNECT data=%d, want 0", g_c_connect_data);
    return 0;
}

static int scen_send(void) {
    CHECK(setup_client_connected(0) == 0, "setup failed");

    /* lenet -> C: three delivery modes */
    uint8_t pay_r[100], pay_u[100], pay_s[60];
    for (int i = 0; i < 100; i++) pay_r[i] = (uint8_t)(i * 3);
    for (int i = 0; i < 100; i++) pay_u[i] = (uint8_t)(i + 100);
    for (int i = 0; i < 60; i++) pay_s[i] = (uint8_t)(255 - i);
    CHECK(lenet_host_send(g_lenet, (uint16_t)g_lenet_peer, 0,
                          LENET_DELIVERY_RELIABLE, pay_r, 100) == 0, "send reliable");
    CHECK(lenet_host_send(g_lenet, (uint16_t)g_lenet_peer, 0,
                          LENET_DELIVERY_UNRELIABLE, pay_u, 100) == 0, "send unreliable");
    CHECK(lenet_host_send(g_lenet, (uint16_t)g_lenet_peer, 1,
                          LENET_DELIVERY_UNSEQUENCED, pay_s, 60) == 0, "send unsequenced");

    WAIT(g_c_pkts == 3, 2000, "enet received %d/3 packets", g_c_pkts);
    CHECK(g_c_ch0len == 200 && memcmp(g_c_ch0, pay_r, 100) == 0
          && memcmp(g_c_ch0 + 100, pay_u, 100) == 0, "reliable+unreliable bytes mismatch");
    CHECK(g_c_ch1len == 60 && memcmp(g_c_ch1, pay_s, 60) == 0, "unsequenced bytes mismatch");

    /* C -> lenet */
    uint8_t rp[100], up[80], sp[40];
    for (int i = 0; i < 100; i++) rp[i] = (uint8_t)(i * 5);
    for (int i = 0; i < 80; i++) up[i] = (uint8_t)(i ^ 0x5A);
    for (int i = 0; i < 40; i++) sp[i] = (uint8_t)(i * 3);
    ENetPacket *p1 = enet_packet_create(rp, 100, ENET_PACKET_FLAG_RELIABLE);
    ENetPacket *p2 = enet_packet_create(up, 80, 0);
    ENetPacket *p3 = enet_packet_create(sp, 40, ENET_PACKET_FLAG_UNSEQUENCED);
    enet_peer_send(g_enet_peer, 0, p1);
    enet_peer_send(g_enet_peer, 0, p2);
    enet_peer_send(g_enet_peer, 1, p3);
    WAIT(g_l_pkts == 3, 2000, "lenet received %d/3 packets", g_l_pkts);
    CHECK(g_l_ch0len == 180 && memcmp(g_l_ch0, rp, 100) == 0
          && memcmp(g_l_ch0 + 100, up, 80) == 0, "reliable+unreliable bytes mismatch (lenet)");
    CHECK(g_l_ch1len == 40 && memcmp(g_l_ch1, sp, 40) == 0, "unsequenced bytes mismatch (lenet)");
    return 0;
}

static int scen_frag(void) {
    CHECK(setup_client_connected(0) == 0, "setup failed");
    static uint8_t big[40000];
    for (size_t i = 0; i < sizeof big; i++)
        big[i] = (uint8_t)(i * 7 + (i >> 8));

    CHECK(lenet_host_send(g_lenet, (uint16_t)g_lenet_peer, 0,
                          LENET_DELIVERY_RELIABLE, big, sizeof big) == 0,
          "lenet fragmented send failed");
    WAIT(g_c_ch0len == sizeof big, 5000, "C received %zu/40000 bytes", g_c_ch0len);
    CHECK(memcmp(g_c_ch0, big, sizeof big) == 0, "fragmented payload mismatch (C side)");

    ENetPacket *pkt = enet_packet_create(big, sizeof big, ENET_PACKET_FLAG_RELIABLE);
    enet_peer_send(g_enet_peer, 0, pkt);
    WAIT(g_l_ch0len == sizeof big, 5000, "lenet received %zu/40000 bytes", g_l_ch0len);
    CHECK(memcmp(g_l_ch0, big, sizeof big) == 0, "fragmented payload mismatch (lenet)");
    return 0;
}

static int scen_disconnect(void) {
    CHECK(setup_client_connected(0) == 0, "setup failed");
    lenet_host_disconnect(g_lenet, (uint16_t)g_lenet_peer, 42);
    WAIT(g_c_disconnected && g_l_disconnected, 2000,
         "disconnect incomplete (c=%d l=%d)", g_c_disconnected, g_l_disconnected);
    CHECK(g_c_disc_data == 42, "enet DISCONNECT data=%d, want 42", g_c_disc_data);
    return 0;
}

static int scen_disconnect_r(void) {
    CHECK(setup_server_connected(0) == 0, "setup failed");
    enet_peer_disconnect(g_enet_peer, 7);
    WAIT(g_c_disconnected && g_l_disconnected, 2000,
         "reverse disconnect incomplete (c=%d l=%d)", g_c_disconnected, g_l_disconnected);
    CHECK(g_l_disc_data == 7, "lenet DISCONNECT data=%d, want 7", g_l_disc_data);
    return 0;
}

static int scen_timeout(void) {
    CHECK(setup_client_connected(0) == 0, "setup failed");
    enet_peer_timeout(g_enet_peer, 4, 200, 600);
    g_lenet_dead = 1;
    WAIT(g_c_disconnected, 3000, "enet peer did not time out");
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: interop <scenario>\n"
                        "scenarios: connect connect_r send frag disconnect disconnect_r timeout\n");
        return 1;
    }
    if (enet_initialize() != 0) { fprintf(stderr, "enet_initialize failed\n"); return 2; }
    fprintf(stderr, "CHECKPOINT: ffi init begin\n");
    lenet_ffi_initialize();
    fprintf(stderr, "CHECKPOINT: initialized\n");

    int rc;
    if (strcmp(argv[1], "connect") == 0) rc = scen_connect();
    else if (strcmp(argv[1], "connect_r") == 0) rc = scen_connect_r();
    else if (strcmp(argv[1], "send") == 0) rc = scen_send();
    else if (strcmp(argv[1], "frag") == 0) rc = scen_frag();
    else if (strcmp(argv[1], "disconnect") == 0) rc = scen_disconnect();
    else if (strcmp(argv[1], "disconnect_r") == 0) rc = scen_disconnect_r();
    else if (strcmp(argv[1], "timeout") == 0) rc = scen_timeout();
    else { fprintf(stderr, "unknown scenario: %s\n", argv[1]); return 1; }

    printf("%s %s\n", rc == 0 ? "PASS" : "FAILED", argv[1]);

    if (g_lenet) lenet_host_destroy(g_lenet);
    if (g_enet) enet_host_destroy(g_enet);
    enet_deinitialize();
    return rc == 0 ? 0 : 1;
}
