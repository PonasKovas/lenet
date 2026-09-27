/*
 * A bad link for the lossy interop test: a UDP proxy on 127.0.0.1 that
 * drops, duplicates, delays and so reorders datagrams between one client
 * and a server.
 *
 *   proxy <listen port> <server port> <seed> <profile>
 *
 * The client sends to <listen port>; the proxy forwards to <server port>
 * from a socket of its own, and the server's answers back the same way.
 * One client at a time: a datagram from a new address makes it the client.
 *
 * Profiles (per datagram, each direction on its own):
 *   clean   forwards everything at once
 *   light   drops 1 in 20, duplicates 1 in 50, delays 0-20 ms
 *   heavy   drops 1 in 5, duplicates 1 in 20, delays 0-40 ms: about a
 *           third of round trips fail (1 in 3 each way makes ENet time
 *           out against itself: some command out of hundreds loses seven
 *           tries in a row)
 *   burst   delays 0-10 ms, and drops everything, both ways, for 200-500
 *           ms every 2-4 s (a burst takes a command's first five tries at
 *           once, since the resend timeout starts near 30 ms; with bursts
 *           every 1-2 s, or random loss on top, ENet times out against
 *           itself on long runs)
 *
 * Every decision comes from <seed>: each direction draws from its own
 * generator, one draw set per datagram, and the burst schedule from a
 * third. So a failure replays as far as the programs on both ends send
 * the same datagrams in the same order (timing moves them a little).
 *
 * Runs until SIGTERM or SIGINT, then prints what it did. With PROXY_LOG
 * set, appends every datagram to that file: time (ms from the start),
 * direction (C = to the client, S = to the server), what happened to it
 * (sent, dropped, burst-dropped) and its bytes in hex.
 */
#define _POSIX_C_SOURCE 200809L
#include <arpa/inet.h>
#include <netinet/in.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#define MAX_DATAGRAM 4096
#define MAX_HELD 8192

typedef struct { uint64_t s; } Rng;

/* splitmix64 */
static uint64_t next(Rng *r) {
    uint64_t z = (r->s += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}

static uint32_t below(Rng *r, uint32_t n) { return n ? (uint32_t)(next(r) % n) : 0; }

typedef struct {
    uint32_t drop, dup;      /* 1 in n; 0 = never */
    uint32_t delay;          /* up to this many ms */
    int bursts;
} Profile;

typedef struct {
    uint64_t due;            /* ms */
    int toServer;
    size_t len;
    uint8_t data[MAX_DATAGRAM];
} Held;

static Held held[MAX_HELD];
static size_t heldCount;

static FILE *logFile;
static uint64_t startMs;

static void logDatagram(uint64_t now, int toServer, char what, const uint8_t *d, size_t n) {
    if (!logFile) return;
    fprintf(logFile, "%llu %c %c ", (unsigned long long)(now - startMs), toServer ? 'S' : 'C', what);
    for (size_t i = 0; i < n; i++) fprintf(logFile, "%02x", d[i]);
    fputc('\n', logFile);
}

static volatile sig_atomic_t stop;
static void onSignal(int sig) { (void)sig; stop = 1; }

static uint64_t nowMs(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000;
}

static int udpSocket(uint16_t port) {
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) { perror("socket"); exit(2); }
    struct sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    a.sin_port = htons(port);
    if (bind(fd, (struct sockaddr *)&a, sizeof a) != 0) { perror("bind"); exit(2); }
    return fd;
}

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "usage: proxy <listen port> <server port> <seed> clean|light|heavy|burst\n");
        return 2;
    }
    uint16_t listenPort = (uint16_t)atoi(argv[1]);
    uint16_t serverPort = (uint16_t)atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    Profile p;
    if (!strcmp(argv[4], "clean")) p = (Profile){0, 0, 0, 0};
    else if (!strcmp(argv[4], "light")) p = (Profile){20, 50, 20, 0};
    else if (!strcmp(argv[4], "heavy")) p = (Profile){5, 20, 40, 0};
    else if (!strcmp(argv[4], "burst")) p = (Profile){0, 0, 10, 1};
    else { fprintf(stderr, "proxy: unknown profile %s\n", argv[4]); return 2; }

    Rng dirRng[2] = {{seed * 3 + 1}, {seed * 3 + 2}};
    Rng burstRng = {seed * 3 + 3};

    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = onSignal;
    sigaction(SIGTERM, &sa, NULL);
    sigaction(SIGINT, &sa, NULL);

    int front = udpSocket(listenPort);   /* the client talks to this */
    int back = udpSocket(0);             /* this talks to the server */
    struct sockaddr_in server;
    memset(&server, 0, sizeof server);
    server.sin_family = AF_INET;
    server.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    server.sin_port = htons(serverPort);
    struct sockaddr_in client;
    int haveClient = 0;

    uint64_t start = nowMs();
    startMs = start;
    if (getenv("PROXY_LOG")) logFile = fopen(getenv("PROXY_LOG"), "w");
    uint64_t burstStart = start + 1000 + below(&burstRng, 2000);
    uint64_t burstEnd = burstStart + 200 + below(&burstRng, 300);
    unsigned long seen[2] = {0, 0}, dropped[2] = {0, 0}, duplicated[2] = {0, 0}, burstDropped = 0;
    unsigned bursts = 0;

    while (!stop) {
        uint64_t now = nowMs();
        if (p.bursts && now >= burstEnd) {
            bursts++;
            burstStart = now + 2000 + below(&burstRng, 2000);
            burstEnd = burstStart + 200 + below(&burstRng, 300);
        }

        /* send what is due, oldest due first among equals */
        for (size_t i = 0; i < heldCount;) {
            if (held[i].due <= now) {
                Held *h = &held[i];
                logDatagram(now, h->toServer, 's', h->data, h->len);
                if (h->toServer)
                    sendto(back, h->data, h->len, 0, (struct sockaddr *)&server, sizeof server);
                else if (haveClient)
                    sendto(front, h->data, h->len, 0, (struct sockaddr *)&client, sizeof client);
                held[i] = held[--heldCount];
            } else i++;
        }

        int wait = 50;
        for (size_t i = 0; i < heldCount; i++) {
            int d = (int)(held[i].due - now);
            if (d < wait) wait = d;
        }
        if (p.bursts) {
            int d = (int)((now < burstStart ? burstStart : burstEnd) - now);
            if (d < wait) wait = d;
        }
        if (wait < 0) wait = 0;

        struct pollfd fds[2] = {{front, POLLIN, 0}, {back, POLLIN, 0}};
        if (poll(fds, 2, wait) <= 0) continue;
        now = nowMs();
        for (int f = 0; f < 2; f++) {
            if (!(fds[f].revents & POLLIN)) continue;
            uint8_t buf[MAX_DATAGRAM];
            struct sockaddr_in from;
            socklen_t fromLen = sizeof from;
            ssize_t n = recvfrom(fds[f].fd, buf, sizeof buf, 0, (struct sockaddr *)&from, &fromLen);
            if (n < 0) continue;
            int toServer = f == 0;
            if (toServer) {
                if (!haveClient || from.sin_port != client.sin_port || from.sin_addr.s_addr != client.sin_addr.s_addr) {
                    client = from;
                    haveClient = 1;
                }
            } else if (from.sin_port != server.sin_port) continue;

            seen[toServer]++;
            Rng *r = &dirRng[toServer];
            /* always the same draws per datagram, whatever the outcome */
            uint32_t dropDraw = below(r, p.drop), dupDraw = below(r, p.dup);
            uint32_t delay1 = below(r, p.delay + 1), delay2 = below(r, p.delay + 1);
            if (p.bursts && now >= burstStart && now < burstEnd) {
                burstDropped++;
                logDatagram(now, toServer, 'b', buf, (size_t)n);
                continue;
            }
            if (p.drop && dropDraw == 0) {
                dropped[toServer]++;
                logDatagram(now, toServer, 'd', buf, (size_t)n);
                continue;
            }
            int copies = p.dup && dupDraw == 0 ? 2 : 1;
            if (copies == 2) duplicated[toServer]++;
            for (int c = 0; c < copies && heldCount < MAX_HELD; c++) {
                Held *h = &held[heldCount++];
                h->due = now + (c == 0 ? delay1 : delay2);
                h->toServer = toServer;
                h->len = (size_t)n;
                memcpy(h->data, buf, (size_t)n);
            }
        }
    }
    if (logFile) fclose(logFile);
    printf("  proxy %s seed %llu: to server %lu (dropped %lu, doubled %lu), to client %lu (dropped %lu, doubled %lu)",
           argv[4], (unsigned long long)seed, seen[1], dropped[1], duplicated[1], seen[0], dropped[0], duplicated[0]);
    if (p.bursts) printf(", %u bursts dropped %lu", bursts, burstDropped);
    printf(", %.1f s\n", (double)(nowMs() - start) / 1000);
    return 0;
}
