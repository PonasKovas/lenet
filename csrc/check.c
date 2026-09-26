/* Smoke check for the Lenet C API: this program intentionally has zero
 * Lean involvement: it includes only lenet.h and links only -llenet. */
#include <lenet.h>
#include <stdio.h>

#define CHECK(cond, msg) \
    do { if (!(cond)) { fprintf(stderr, "check failed: %s\n", msg); return 1; } } while (0)

int main(void) {
    lenet_initialize();
    lenet_host *h = lenet_host_create(0, 0, 16, 2, 0, 0, 0);
    CHECK(h != NULL, "create");

    int32_t peer = lenet_host_connect(h, 0x0100007F /* 127.0.0.1 */, 40010, 2, 0);
    CHECK(peer >= 0, "connect");
    CHECK(lenet_host_send(h, (uint16_t)peer, 0, LENET_RELIABLE, "hello", 5) == -1,
          "send before the connection completes must fail");
    CHECK(lenet_host_send(h, 999, 0, LENET_RELIABLE, "hello", 5) == -1,
          "send to an unknown peer must fail");

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

    lenet_host_destroy(h);
    printf("lenet C API OK\n");
    return 0;
}
