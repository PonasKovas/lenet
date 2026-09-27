/*
 * ENet echo peer for the Lenet.Net interop test: a real ENet host in its
 * own process, talking over real UDP sockets to a Lean program that uses
 * Lenet.Net (test/NetInterop.lean).
 *
 *   echo server <port>   echoes every packet back on its channel, with its
 *                        flags, until the peer disconnects
 *   echo client <port>   connects to a Lenet.Net echo server, sends the
 *                        packet set, checks every reliable packet comes
 *                        back once, in order and intact, then disconnects
 *
 * The packet set (same in NetInterop.lean): 30 reliable packets on channel
 * 0, packet i of 1 + (i * 97) % 3000 bytes, and a fragmented 20000-byte
 * one; byte j of packet i is (j * 31 + i) % 251. Plus 5 unsequenced ones
 * on channel 1, which may be lost and are not checked.
 *
 * Exit code 0 = passed. Both give up after 10 s.
 */
#include <enet/enet.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define RELIABLE 31
#define GIVE_UP_MS 10000

static uint32_t now_ms(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint32_t)(t.tv_sec * 1000 + t.tv_nsec / 1000000);
}

static size_t packet_size(int i) { return i == 30 ? 20000 : 1 + (size_t)(i * 97) % 3000; }

static void fill(uint8_t *buf, int i) {
    for (size_t j = 0; j < packet_size(i); j++) buf[j] = (uint8_t)((j * 31 + (size_t)i) % 251);
}

static ENetHost *make_host(uint16_t port) {
    ENetAddress a;
    memset(&a, 0, sizeof a);
    enet_address_set_host(&a, "127.0.0.1");
    a.port = port;
    ENetHost *h = enet_host_create(port ? &a : NULL, 4, 2, 0, 0);
    if (!h) { fprintf(stderr, "FATAL: enet_host_create\n"); exit(2); }
    return h;
}

static int run_server(uint16_t port) {
    ENetHost *host = make_host(port);
    uint32_t start = now_ms();
    int echoed = 0;
    while (now_ms() - start < GIVE_UP_MS) {
        ENetEvent ev;
        while (enet_host_service(host, &ev, 5) > 0) {
            switch (ev.type) {
            case ENET_EVENT_TYPE_CONNECT:
                printf("  enet: CONNECT data=%u\n", ev.data);
                break;
            case ENET_EVENT_TYPE_RECEIVE: {
                ENetPacket *back = enet_packet_create(ev.packet->data, ev.packet->dataLength,
                                                      ev.packet->flags & ~ENET_PACKET_FLAG_SENT);
                enet_peer_send(ev.peer, ev.channelID, back);
                enet_packet_destroy(ev.packet);
                echoed++;
                break;
            }
            case ENET_EVENT_TYPE_DISCONNECT:
                printf("  enet: DISCONNECT data=%u after %d echoes\n", ev.data, echoed);
                enet_host_destroy(host);
                return 0;
            default:
                break;
            }
        }
    }
    fprintf(stderr, "FAIL: enet echo server: no disconnect within %d ms\n", GIVE_UP_MS);
    return 1;
}

static int run_client(uint16_t port) {
    ENetHost *host = make_host(0);
    ENetAddress to;
    enet_address_set_host(&to, "127.0.0.1");
    to.port = port;
    ENetPeer *peer = enet_host_connect(host, &to, 2, 7);
    if (!peer) { fprintf(stderr, "FATAL: enet_host_connect\n"); return 2; }
    static uint8_t buf[20000];
    uint32_t start = now_ms();
    int connected = 0, back = 0, disconnecting = 0;
    while (now_ms() - start < GIVE_UP_MS) {
        ENetEvent ev;
        while (enet_host_service(host, &ev, 5) > 0) {
            switch (ev.type) {
            case ENET_EVENT_TYPE_CONNECT:
                printf("  enet: CONNECT\n");
                connected = 1;
                for (int i = 0; i < RELIABLE; i++) {
                    fill(buf, i);
                    enet_peer_send(peer, 0, enet_packet_create(buf, packet_size(i), ENET_PACKET_FLAG_RELIABLE));
                }
                for (int i = 0; i < 5; i++) {
                    fill(buf, i);
                    enet_peer_send(peer, 1, enet_packet_create(buf, 64, ENET_PACKET_FLAG_UNSEQUENCED));
                }
                break;
            case ENET_EVENT_TYPE_RECEIVE:
                if (ev.channelID == 0) {
                    if (back >= RELIABLE) {
                        fprintf(stderr, "FAIL: more echoes than packets sent\n");
                        return 1;
                    }
                    fill(buf, back);
                    if (ev.packet->dataLength != packet_size(back) ||
                        memcmp(ev.packet->data, buf, packet_size(back)) != 0) {
                        fprintf(stderr, "FAIL: echo %d is not packet %d (%u bytes)\n", back, back,
                                (unsigned)ev.packet->dataLength);
                        return 1;
                    }
                    back++;
                    if (back == RELIABLE && !disconnecting) {
                        enet_peer_disconnect(peer, 9);
                        disconnecting = 1;
                    }
                }
                enet_packet_destroy(ev.packet);
                break;
            case ENET_EVENT_TYPE_DISCONNECT:
                if (!disconnecting) {
                    fprintf(stderr, "FAIL: disconnected after %d of %d echoes\n", back, RELIABLE);
                    return 1;
                }
                printf("  enet: all %d reliable echoes back in order; DISCONNECT\n", back);
                enet_host_destroy(host);
                return 0;
            default:
                break;
            }
        }
    }
    fprintf(stderr, "FAIL: enet client gave up (connected %d, %d of %d echoes)\n", connected, back, RELIABLE);
    return 1;
}

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: echo server|client <port>\n"); return 2; }
    if (enet_initialize() != 0) { fprintf(stderr, "FATAL: enet_initialize\n"); return 2; }
    uint16_t port = (uint16_t)atoi(argv[2]);
    int r = strcmp(argv[1], "server") == 0 ? run_server(port)
          : strcmp(argv[1], "client") == 0 ? run_client(port) : 2;
    enet_deinitialize();
    return r;
}
