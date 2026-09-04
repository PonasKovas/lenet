/* Smoke check for the Lenet C API: this program intentionally has zero
 * Lean involvement — it includes only lenet.h and links only -llenet. */
#include <lenet.h>
#include <stdio.h>

int main(void) {
    lenet_initialize();
    lenet_host *h = lenet_host_create(0, 0, 16, 2, 0, 0, 0);
    if (h == NULL) { fprintf(stderr, "create failed\n"); return 1; }
    int32_t peer = lenet_host_connect(h, 0x0100007F /* 127.0.0.1 */, 40010, 2, 0);
    if (peer < 0) { fprintf(stderr, "connect failed\n"); return 1; }
    uint8_t payload[64] = {0};
    if (lenet_host_send(h, (uint16_t)peer, 0, LENET_RELIABLE,
                        (const uint8_t *)"hello", 5) != 0) {
        fprintf(stderr, "send should fail only after connection; got err (ok: unconnected)\n");
    }
    lenet_host_service(h, 0);
    lenet_event ev; size_t plen = 0;
    while (lenet_host_poll_event(h, &ev, payload, sizeof payload, &plen) == 1) {}
    lenet_datagram dg;
    while (lenet_host_poll_outgoing(h, &dg) == 1) { /* drain */ }
    lenet_host_destroy(h);
    printf("lenet C API OK\n");
    return 0;
}