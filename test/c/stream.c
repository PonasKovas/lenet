/*
 * ENet side of the lossy interop test (`make -C test lossy-interop`): a
 * real ENet host in its own process, talking to Lenet.Net
 * (test/NetStream.lean) through test/c/proxy.c.
 *
 *   stream server <port> <rounds> <per round> [long]
 *   stream client <port> <rounds> <per round> [long]
 *
 * Both ends send the same stream and check the other's. Round r (one every
 * 10 ms from the connect on) sends, with P = <per round>:
 *   channel 0: reliable packets rP .. rP+P-1, every tenth one fragmented
 *   channel 1: reliable packets rP .. rP+P-1, then unreliable packet r
 *   channel 2: unreliable-fragment packet r (always fragmented), then
 *              unsequenced packet r
 * A packet is its kind (byte 0: 0 reliable, 1 unreliable, 2 unsequenced,
 * 3 done), its index (bytes 1-4, big-endian) and filler bytes; its size
 * and filler follow from kind, channel and index (`size`, `fill`).
 *
 * Checked on receipt: every packet is intact; reliable ones arrive once
 * each and in order on both channels; unreliable ones at most once and in
 * order; unsequenced ones at most once.
 *
 * The end: the server, once it has every reliable packet and nothing of
 * its own is queued or unacknowledged, sends "done" (kind 3, the next
 * reliable packet on channel 0). The client, once it has every reliable
 * packet and "done" and nothing of its own is queued or unacknowledged,
 * disconnects with data 9. The server passes on that DISCONNECT; the client
 * on the DISCONNECT that follows. If the link lost the ACK of its
 * DISCONNECT, nothing answers again (the server is gone by then, in ENet
 * as in Lenet), so after 5 s the client passes without it and says so.
 *
 * `long` sets both ends' timeouts to limit 256, minimum 20 s, maximum
 * 60 s (enet_peer_timeout), for links too lossy for the defaults.
 *
 * Exit code 0 = passed. Gives up after 90 s without receiving a packet
 * (longer than any timeout, so a stuck link ends in a timeout first).
 */
#include <enet/enet.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

enum { RELIABLE, UNRELIABLE, UNSEQUENCED, DONE };

static uint32_t now_ms(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint32_t)(t.tv_sec * 1000 + t.tv_nsec / 1000000);
}

static size_t size(int kind, int ch, uint32_t i) {
    switch (kind) {
    case RELIABLE:
        if (ch == 0) return i % 10 == 3 ? 3000 + (i * 337) % 6000 : 5 + (i * 97) % 1000;
        return 5 + (i * 53) % 400;
    case UNRELIABLE:
        return ch == 1 ? 5 + (i * 71) % 1100 : 1500 + (i * 211) % 3000;
    case UNSEQUENCED:
        return 5 + (i * 13) % 200;
    default:
        return 5;
    }
}

static void fill(uint8_t *buf, int kind, int ch, uint32_t i) {
    size_t n = size(kind, ch, i);
    buf[0] = (uint8_t)kind;
    buf[1] = (uint8_t)(i >> 24); buf[2] = (uint8_t)(i >> 16); buf[3] = (uint8_t)(i >> 8); buf[4] = (uint8_t)i;
    for (size_t j = 5; j < n; j++) buf[j] = (uint8_t)((j * 31 + i + (uint32_t)kind * 7 + (uint32_t)ch * 3) % 251);
}

static uint8_t buf[16384], want[16384];

static void send_one(ENetPeer *peer, int kind, int ch, uint32_t i, enet_uint32 flags) {
    fill(buf, kind, ch, i);
    enet_peer_send(peer, (enet_uint8)ch, enet_packet_create(buf, size(kind, ch, i), flags));
}

typedef struct {
    uint32_t total;             /* reliable packets per channel */
    uint32_t rounds;
    uint32_t reliable[2];       /* next expected, channels 0 and 1 */
    int64_t unreliable[3];      /* last seen, channels 1 and 2 */
    uint32_t unreliableSeen[3];
    uint8_t *unsequenced;       /* seen, by index */
    uint32_t unsequencedSeen;
    int done;
} Received;

/* Checks one packet; returns an error message or NULL. */
static const char *receive(Received *r, int ch, const uint8_t *d, size_t n) {
    static char err[160];
    if (n < 5) return "packet under 5 bytes";
    int kind = d[0];
    uint32_t i = (uint32_t)d[1] << 24 | (uint32_t)d[2] << 16 | (uint32_t)d[3] << 8 | d[4];
    if (kind > DONE || ch > 2) return "unknown kind or channel";
    if (n != size(kind, ch, i)) {
        snprintf(err, sizeof err, "kind %d channel %d packet %u has %zu bytes, not %zu", kind, ch, i, n, size(kind, ch, i));
        return err;
    }
    fill(want, kind, ch, i);
    if (memcmp(d, want, n) != 0) {
        snprintf(err, sizeof err, "kind %d channel %d packet %u is corrupt", kind, ch, i);
        return err;
    }
    switch (kind) {
    case RELIABLE:
        if (ch > 1 || i != r->reliable[ch]) {
            snprintf(err, sizeof err, "reliable packet %u on channel %d, expected %u", i, ch, ch > 1 ? 0 : r->reliable[ch]);
            return err;
        }
        r->reliable[ch]++;
        return NULL;
    case UNRELIABLE:
        if (ch == 0 || (int64_t)i <= r->unreliable[ch]) {
            snprintf(err, sizeof err, "unreliable packet %u on channel %d after %lld", i, ch, (long long)r->unreliable[ch]);
            return err;
        }
        r->unreliable[ch] = i;
        r->unreliableSeen[ch]++;
        return NULL;
    case UNSEQUENCED:
        if (ch != 2 || i >= r->rounds || r->unsequenced[i]) {
            snprintf(err, sizeof err, "unsequenced packet %u twice or out of range", i);
            return err;
        }
        r->unsequenced[i] = 1;
        r->unsequencedSeen++;
        return NULL;
    default:
        if (ch != 0 || r->done || r->reliable[0] != r->total) return "done before every reliable packet, or twice";
        r->done = 1;
        return NULL;
    }
}

static int all_reliable(const Received *r) { return r->reliable[0] == r->total && r->reliable[1] == r->total; }

static int idle(const ENetPeer *p) {
    return enet_list_empty(&p->sentReliableCommands) && enet_list_empty(&p->outgoingSendReliableCommands) &&
           enet_list_empty(&p->outgoingCommands) && p->reliableDataInTransit == 0;
}

/* What the host holds for the connection: printed when nothing has come in
 * for a while, to see where a stuck link is stuck. */
static void stall_report(const char *me, const Received *r, uint32_t sentRounds, ENetHost *host, ENetPeer *p) {
    fprintf(stderr, "  stall %s: got %u+%u of %u, rounds %u, state %d, rtt %u/%u, transit %u/%u, queued %zu+%zu, in flight %zu",
            me, r->reliable[0], r->reliable[1], r->total, sentRounds, p->state, p->roundTripTime,
            p->roundTripTimeVariance, p->reliableDataInTransit, p->windowSize, enet_list_size(&p->outgoingCommands),
            enet_list_size((ENetList *)&p->outgoingSendReliableCommands), enet_list_size((ENetList *)&p->sentReliableCommands));
    if (!enet_list_empty(&p->sentReliableCommands)) {
        ENetOutgoingCommand *c = (ENetOutgoingCommand *)enet_list_front(&p->sentReliableCommands);
        fprintf(stderr, " (oldest ch %u seq %u tries %u rto %u age %u)", c->command.header.channelID,
                c->reliableSequenceNumber, c->sendAttempts, c->roundTripTimeout, host->serviceTime - c->sentTime);
    }
    if (!enet_list_empty(&p->outgoingSendReliableCommands)) {
        ENetOutgoingCommand *c = (ENetOutgoingCommand *)enet_list_front(&p->outgoingSendReliableCommands);
        fprintf(stderr, " (first queued ch %u seq %u tries %u)", c->command.header.channelID, c->reliableSequenceNumber,
                c->sendAttempts);
    }
    fprintf(stderr, ", channels");
    for (size_t i = 0; i < p->channelCount; i++) {
        ENetChannel *c = &p->channels[i];
        fprintf(stderr, " [out %u in %u staged %zu used %04x windows", c->outgoingReliableSequenceNumber,
                c->incomingReliableSequenceNumber, enet_list_size(&c->incomingReliableCommands), c->usedReliableWindows);
        for (int w = 0; w < ENET_PEER_RELIABLE_WINDOWS; w++) fprintf(stderr, " %u", c->reliableWindows[w]);
        fprintf(stderr, "]");
    }
    fprintf(stderr, "\n");
}

static int run(int isServer, uint16_t port, uint32_t rounds, uint32_t per, int longTimeouts) {
    ENetAddress a;
    memset(&a, 0, sizeof a);
    enet_address_set_host(&a, "127.0.0.1");
    a.port = port;
    ENetHost *host = enet_host_create(isServer ? &a : NULL, 4, 3, 0, 0);
    if (!host) { fprintf(stderr, "FATAL: enet_host_create\n"); return 2; }
    ENetPeer *peer = NULL;
    if (!isServer) {
        peer = enet_host_connect(host, &a, 3, 7);
        if (!peer) { fprintf(stderr, "FATAL: enet_host_connect\n"); return 2; }
        if (longTimeouts) enet_peer_timeout(peer, 256, 20000, 60000);
    }
    const char *me = isServer ? "enet server" : "enet client";
    Received r;
    memset(&r, 0, sizeof r);
    r.total = rounds * per;
    r.unreliable[1] = r.unreliable[2] = -1;
    r.rounds = rounds;
    r.unsequenced = calloc(rounds ? rounds : 1, 1);

    uint32_t start = now_ms(), connectedAt = 0, lastReceive = start, lastReport = 0;
    uint32_t sentRounds = 0;
    int connected = 0, doneSent = 0, disconnecting = 0;
    uint32_t disconnectedAt = 0;
    while (now_ms() - lastReceive < 90000) {
        if (connected && now_ms() - lastReceive >= 2000 && now_ms() - lastReport >= 2000) {
            stall_report(me, &r, sentRounds, host, peer);
            lastReport = now_ms();
        }
        if (connected) {
            while (sentRounds < rounds && now_ms() - connectedAt >= sentRounds * 10) {
                uint32_t k = sentRounds;
                for (uint32_t i = k * per; i < (k + 1) * per; i++)
                    send_one(peer, RELIABLE, 0, i, ENET_PACKET_FLAG_RELIABLE);
                for (uint32_t i = k * per; i < (k + 1) * per; i++)
                    send_one(peer, RELIABLE, 1, i, ENET_PACKET_FLAG_RELIABLE);
                send_one(peer, UNRELIABLE, 1, k, 0);
                send_one(peer, UNRELIABLE, 2, k, ENET_PACKET_FLAG_UNRELIABLE_FRAGMENT);
                send_one(peer, UNSEQUENCED, 2, k, ENET_PACKET_FLAG_UNSEQUENCED);
                sentRounds++;
            }
            if (sentRounds == rounds && all_reliable(&r) && idle(peer)) {
                if (isServer && !doneSent) {
                    send_one(peer, DONE, 0, r.total, ENET_PACKET_FLAG_RELIABLE);
                    doneSent = 1;
                } else if (!isServer && r.done && !disconnecting) {
                    enet_peer_disconnect(peer, 9);
                    disconnecting = 1;
                    disconnectedAt = now_ms();
                }
            }
            if (disconnecting && now_ms() - disconnectedAt >= 5000) {
                printf("  %s: %u reliable per channel in order; no ACK of the DISCONNECT in 5 s (lost), %.1f s\n",
                       me, r.total, (double)(now_ms() - start) / 1000);
                enet_peer_reset(peer);
                enet_host_destroy(host);
                free(r.unsequenced);
                return 0;
            }
        }
        ENetEvent ev;
        while (enet_host_service(host, &ev, 5) > 0) {
            switch (ev.type) {
            case ENET_EVENT_TYPE_CONNECT:
                if (connected) { fprintf(stderr, "FAIL: %s: a second connection\n", me); return 1; }
                peer = ev.peer;
                if (longTimeouts) enet_peer_timeout(peer, 256, 20000, 60000);
                connected = 1;
                connectedAt = now_ms();
                break;
            case ENET_EVENT_TYPE_RECEIVE: {
                lastReceive = now_ms();
                const char *err = receive(&r, ev.channelID, ev.packet->data, ev.packet->dataLength);
                enet_packet_destroy(ev.packet);
                if (err) { fprintf(stderr, "FAIL: %s: %s\n", me, err); return 1; }
                break;
            }
            case ENET_EVENT_TYPE_DISCONNECT:
                if (isServer ? !(doneSent && ev.data == 9) : !disconnecting) {
                    fprintf(stderr, "FAIL: %s: DISCONNECT (data %u) before the end: %u+%u of %u reliable, done %d\n",
                            me, ev.data, r.reliable[0], r.reliable[1], r.total, r.done);
                    return 1;
                }
                printf("  %s: %u reliable per channel in order; unreliable %u+%u, unsequenced %u of %u; clean end, %.1f s\n",
                       me, r.total, r.unreliableSeen[1], r.unreliableSeen[2], r.unsequencedSeen, rounds,
                       (double)(now_ms() - start) / 1000);
                enet_host_destroy(host);
                free(r.unsequenced);
                return 0;
            default:
                break;
            }
        }
    }
    fprintf(stderr, "FAIL: %s gave up: connected %d, rounds %u of %u, reliable %u+%u of %u, done %d, idle %d\n", me,
            connected, sentRounds, rounds, r.reliable[0], r.reliable[1], r.total, r.done, peer ? idle(peer) : 0);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5 || argc > 6 || (strcmp(argv[1], "server") && strcmp(argv[1], "client")) ||
        (argc == 6 && strcmp(argv[5], "long"))) {
        fprintf(stderr, "usage: stream server|client <port> <rounds> <per round> [long]\n");
        return 2;
    }
    if (enet_initialize() != 0) { fprintf(stderr, "FATAL: enet_initialize\n"); return 2; }
    int r = run(!strcmp(argv[1], "server"), (uint16_t)atoi(argv[2]), (uint32_t)atoi(argv[3]),
                (uint32_t)atoi(argv[4]), argc == 6);
    enet_deinitialize();
    return r;
}
