/* Smoke check for the Lenet C API: this program intentionally has zero
 * Lean involvement: it includes only lenet.h and links only -llenet. */
#include <lenet.h>
#include <stdio.h>
#include <string.h>

#define CHECK(cond, msg) \
    do { if (!(cond)) { fprintf(stderr, "check failed: %s\n", msg); return 1; } } while (0)

#define LOCALHOST 0x0100007F /* 127.0.0.1 in network byte order */

/* Services `from` at `now` and hands every datagram it produces to `to`,
 * as if sent from port `from_port`. */
static void route(lenet_host *from, uint16_t from_port, lenet_host *to, uint32_t now) {
    lenet_datagram dg;
    lenet_host_service(from, now);
    while (lenet_host_poll_outgoing(from, &dg) == 1)
        lenet_host_handle_datagram(to, now, LOCALHOST, from_port, dg.data, dg.len);
}

/* Two hosts in one process: each one's outgoing bytes are its own, and an
 * event whose payload does not fit the buffer is kept, not lost. */
static int check_pair(void) {
    lenet_host *a = lenet_host_create(0, 0, 4, 2, 0, 0, 0);
    lenet_host *b = lenet_host_create(0, 0, 4, 2, 0, 0, 0);
    CHECK(a != NULL && b != NULL, "create two hosts");

    /* both connect: polling b must not touch what a's datagram points to */
    CHECK(lenet_host_connect(a, LOCALHOST, 2, 2, 0) >= 0, "connect a");
    CHECK(lenet_host_connect(b, LOCALHOST, 1, 2, 0) >= 0, "connect b");
    lenet_datagram da, db;
    uint8_t copy[4096];
    CHECK(lenet_host_service(a, 0) == 0 && lenet_host_poll_outgoing(a, &da) == 1, "a's CONNECT");
    memcpy(copy, da.data, da.len);
    CHECK(lenet_host_service(b, 0) == 0 && lenet_host_poll_outgoing(b, &db) == 1, "b's CONNECT");
    CHECK(da.data != db.data, "two hosts share an outgoing buffer");
    CHECK(memcmp(copy, da.data, da.len) == 0, "polling b changed a's datagram");
    lenet_host_destroy(b);

    /* a connects to a fresh b, then sends it 100 bytes */
    b = lenet_host_create(0, 0, 4, 2, 0, 0, 0);
    CHECK(b != NULL, "create b again");
    lenet_peer_reset(a, 0);
    int32_t peer = lenet_host_connect(a, LOCALHOST, 2, 2, 0);
    CHECK(peer >= 0, "connect a to b");
    for (uint32_t t = 0; t < 20; t++) {
        route(a, 1, b, t);
        route(b, 2, a, t);
    }
    lenet_event ev;
    uint8_t payload[200];
    size_t plen = 0;
    CHECK(lenet_host_poll_event(a, &ev, payload, sizeof payload, &plen) == 1 &&
          ev.type == LENET_EVENT_CONNECT, "a connected");
    CHECK(lenet_host_poll_event(b, &ev, payload, sizeof payload, &plen) == 1 &&
          ev.type == LENET_EVENT_CONNECT, "b connected");
    uint8_t msg[100];
    for (int i = 0; i < 100; i++) msg[i] = (uint8_t)(i * 7);
    CHECK(lenet_host_send(a, (uint16_t)peer, 0, LENET_RELIABLE, msg, sizeof msg) == 0, "send");
    for (uint32_t t = 20; t < 25; t++) {
        route(a, 1, b, t);
        route(b, 2, a, t);
    }
    plen = 0;
    CHECK(lenet_host_poll_event(b, &ev, NULL, 0, &plen) == -2 && plen == 100,
          "NULL buffer: the size, and the event kept");
    CHECK(lenet_host_poll_event(b, &ev, payload, 10, &plen) == -2 && plen == 100,
          "small buffer: the event kept");
    CHECK(lenet_host_poll_event(b, &ev, payload, sizeof payload, &plen) == 1 &&
          ev.type == LENET_EVENT_RECEIVE && plen == 100 && memcmp(payload, msg, 100) == 0,
          "the kept event, whole");
    CHECK(lenet_host_poll_event(b, &ev, payload, sizeof payload, &plen) == 0, "then nothing");
    lenet_host_destroy(a);
    lenet_host_destroy(b);
    return 0;
}

int main(void) {
    lenet_initialize();
    CHECK(lenet_host_create(0, 0, 4096, 2, 0, 0, 0) == NULL, "more than 4095 peers must fail");
    lenet_host *h = lenet_host_create(0, 0, 16, 2, 0, 0, 0);
    CHECK(h != NULL, "create");

    int32_t peer = lenet_host_connect(h, 0x0100007F /* 127.0.0.1 */, 40010, 2, 0);
    CHECK(peer >= 0, "connect");
    CHECK(lenet_host_send(h, (uint16_t)peer, 0, LENET_RELIABLE, "hello", 5) == -1,
          "send before the connection completes must fail");
    CHECK(lenet_host_send(h, 999, 0, LENET_RELIABLE, "hello", 5) == -1,
          "send to an unknown peer must fail");
    /* sizes are checked before anything is read: these lengths lie */
    CHECK(lenet_host_send(h, (uint16_t)peer, 0, LENET_RELIABLE, "x",
                          (size_t)LENET_MAX_PACKET_SIZE + 1) == -1,
          "a packet over the maximum size must fail");
    CHECK(lenet_host_handle_datagram(h, 0, 0x0100007F, 40010, "x", 70000) == -1,
          "a datagram longer than UDP allows must fail");

    CHECK(lenet_host_service(h, 0) == 0, "service");
    lenet_datagram dg;
    int datagrams = 0;
    while (lenet_host_poll_outgoing(h, &dg) == 1) datagrams++;
    CHECK(datagrams == 1, "one CONNECT datagram");
    uint32_t deadline;
    CHECK(lenet_host_next_deadline(h, &deadline) == 1, "a retransmit deadline");

    lenet_event ev;
    uint8_t payload[64];
    size_t plen = 0;
    CHECK(lenet_host_poll_event(h, &ev, payload, sizeof payload, &plen) == 0, "no events");

    lenet_peer_info info;
    CHECK(lenet_peer_get_info(h, (uint16_t)peer, &info) == 0, "peer info");
    CHECK(info.state == LENET_PEER_STATE_CONNECTING, "peer info: state");
    CHECK(info.ip == 0x0100007F && info.port == 40010, "peer info: address");
    CHECK(lenet_peer_get_info(h, 999, &info) == -1, "peer info of an unknown peer must fail");

    lenet_peer_ping_interval(h, (uint16_t)peer, 250);
    lenet_host_bandwidth_limit(h, 100000, 50000);
    lenet_host_channel_limit(h, 4);

    /* disconnect_now: one DISCONNECT goes out, then the slot is free */
    lenet_peer_disconnect_now(h, (uint16_t)peer, 7);
    CHECK(lenet_host_flush(h, 10) == 0, "flush");
    datagrams = 0;
    while (lenet_host_poll_outgoing(h, &dg) == 1) datagrams++;
    CHECK(datagrams == 1, "one DISCONNECT datagram");
    CHECK(lenet_peer_get_info(h, (uint16_t)peer, &info) == 0 &&
          info.state == LENET_PEER_STATE_DISCONNECTED, "slot freed after disconnect_now");
    CHECK(lenet_host_poll_event(h, &ev, payload, sizeof payload, &plen) == 0,
          "disconnect_now reports no event");

    peer = lenet_host_connect(h, 0x0100007F, 40010, 2, 0);
    CHECK(peer >= 0, "reconnect");
    lenet_peer_reset(h, (uint16_t)peer);
    CHECK(lenet_peer_get_info(h, (uint16_t)peer, &info) == 0 &&
          info.state == LENET_PEER_STATE_DISCONNECTED, "reset frees the slot");

    lenet_host_destroy(h);
    if (check_pair() != 0) return 1;
    printf("lenet C API OK\n");
    return 0;
}
