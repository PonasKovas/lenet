/*
 * ENet compatibility recorder harness.
 *
 * Runs two real ENet hosts (client + server) inside one process, with all
 * UDP traffic routed through an in-process proxy socket so every datagram
 * byte can be logged. Produces a deterministic, human-readable trace file:
 *
 *   A <ms> <ROLE> <API call>     application-level call made by the scenario
 *   E <ms> <ROLE> <event>        event returned by enet_host_service
 *   N <ms> <DIR> hex=...         raw datagram on the wire (DIR = C2S | S2C)
 *
 * Usage: harness record <scenario>
 * Writes: traces/<scenario>.trace   (run from the test/ directory)
 */
#include <enet/enet.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <errno.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/select.h>
#include <fcntl.h>

#define PROXY_PORT  40000
#define CLIENT_PORT 40001
#define SERVER_PORT 40002
#define PROXY2_PORT  40010
#define CLIENT2_PORT 40011

static FILE *trace_file;
static struct timespec t_start;

static uint64_t now_ms(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)(t.tv_sec * 1000 + t.tv_nsec / 1000000)
         - (uint64_t)(t_start.tv_sec * 1000 + t_start.tv_nsec / 1000000);
}

static void hex_encode(const unsigned char *data, size_t len, char *out) {
    static const char d[] = "0123456789abcdef";
    for (size_t i = 0; i < len; i++) {
        out[2 * i]     = d[(data[i] >> 4) & 0xF];
        out[2 * i + 1] = d[data[i] & 0xF];
    }
    out[2 * len] = 0;
}

static void log_datagram(const char *dir, const unsigned char *buf, ssize_t len) {
    static char hex[2 * 65536 + 1];
    hex_encode(buf, (size_t)len, hex);
    fprintf(trace_file, "N %llu %s hex=%s\n",
            (unsigned long long)now_ms(), dir, hex);
}

static void log_event(const char *role, ENetEvent *ev) {
    static char hex[2 * 1024 * 1024 + 1];
    switch (ev->type) {
    case ENET_EVENT_TYPE_CONNECT:
        fprintf(trace_file, "E %llu %s CONNECT peer=%u data=%u\n",
                (unsigned long long)now_ms(), role,
                ev->peer->incomingPeerID, ev->data);
        break;
    case ENET_EVENT_TYPE_RECEIVE: {
        size_t n = ev->packet->dataLength;
        if (n > 1024 * 1024) n = 1024 * 1024; /* traces stay bounded */
        hex_encode(ev->packet->data, n, hex);
        fprintf(trace_file, "E %llu %s RECEIVE peer=%u ch=%u flags=%u hex=%s\n",
                (unsigned long long)now_ms(), role,
                ev->peer->incomingPeerID, ev->channelID, ev->packet->flags, hex);
        enet_packet_destroy(ev->packet);
        break;
    }
    case ENET_EVENT_TYPE_DISCONNECT:
        fprintf(trace_file, "E %llu %s DISCONNECT peer=%u data=%u\n",
                (unsigned long long)now_ms(), role,
                ev->peer->incomingPeerID, ev->data);
        break;
    default:
        break;
    }
}

/* Drain all pending events of one host, logging each.
 * Captures the connected peer handle (needed for later scripted actions). */
static void drain_events(ENetHost *host, const char *role, ENetPeer **peer_out) {
    ENetEvent ev;
    while (enet_host_service(host, &ev, 0) > 0) {
        if (ev.type == ENET_EVENT_TYPE_CONNECT && peer_out != NULL)
            *peer_out = ev.peer;
        log_event(role, &ev);
    }
}

/* ---------------- proxy ---------------- */

static int proxy_fd = -1;    /* client1 <-> server */
static int proxy2_fd = -1;   /* client2 <-> server */
static struct sockaddr_in client_addr, client2_addr, server_addr;

static int make_udp(uint16_t port) {
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) { perror("socket"); exit(1); }
    struct sockaddr_in a;
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    a.sin_port = htons(port);
    if (bind(fd, (struct sockaddr *)&a, sizeof a) < 0) { perror("bind"); exit(1); }
    return fd;
}

static void proxy_init(void) {
    proxy_fd = make_udp(PROXY_PORT);
    proxy2_fd = make_udp(PROXY2_PORT);
    int flags = fcntl(proxy_fd, F_GETFL, 0);
    fcntl(proxy_fd, F_SETFL, flags | O_NONBLOCK);
    flags = fcntl(proxy2_fd, F_GETFL, 0);
    fcntl(proxy2_fd, F_SETFL, flags | O_NONBLOCK);
    memset(&client_addr, 0, sizeof client_addr);
    memset(&client2_addr, 0, sizeof client2_addr);
    memset(&server_addr, 0, sizeof server_addr);
    client_addr.sin_family = AF_INET;
    client_addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    client_addr.sin_port = htons(CLIENT_PORT);
    client2_addr = client_addr;
    client2_addr.sin_port = htons(CLIENT2_PORT);
    server_addr = client_addr;
    server_addr.sin_port = htons(SERVER_PORT);
}

/* Forward + log every pending datagram on one proxy socket. Direction by
 * source port; datagrams from the server go back to this proxy's client. */
static void proxy_pump_fd(int fd, const char *c2s, const char *s2c,
                          const struct sockaddr_in *to_client) {
    static unsigned char buf[64 * 1024];
    for (;;) {
        struct sockaddr_in from;
        socklen_t fromlen = sizeof from;
        ssize_t n = recvfrom(fd, buf, sizeof buf, 0,
                             (struct sockaddr *)&from, &fromlen);
        if (n < 0) return; /* EWOULDBLOCK */
        if (ntohs(from.sin_port) == SERVER_PORT) {
            log_datagram(s2c, buf, n);
            sendto(fd, buf, n, 0, (struct sockaddr *)to_client, sizeof *to_client);
        } else {
            log_datagram(c2s, buf, n);
            sendto(fd, buf, n, 0, (struct sockaddr *)&server_addr, sizeof server_addr);
        }
    }
}

static void proxy_pump(void) {
    proxy_pump_fd(proxy_fd, "C2S", "S2C", &client_addr);
    proxy_pump_fd(proxy2_fd, "D2S", "S2D", &client2_addr);
}

/* ---------------- scenario script ---------------- */

typedef enum {
    ACT_CONNECT,      /* role connects to the proxy address       */
    ACT_SEND,         /* role sends payload on a channel          */
    ACT_BROADCAST,    /* server broadcasts payload on a channel   */
    ACT_DISCONNECT,   /* role disconnects its peer                */
    ACT_DISCONNECT_LATER, /* role defers disconnect until flushed */
    ACT_PEER_TIMEOUT, /* tighten peer timeout for fast recording  */
    ACT_STOP_CLIENT   /* stop servicing the client host entirely  */
} ActionKind;

typedef enum { ROLE_C, ROLE_S, ROLE_D } Role;

typedef struct {
    uint32_t at_ms;
    ActionKind kind;
    Role role;
    uint32_t ch;        /* SEND: channel            */
    uint32_t flags;     /* SEND: packet flags       */
    const unsigned char *data; /* SEND: payload     */
    uint32_t data_len;
    uint32_t a, b, c;   /* generic args             */
} Action;

typedef struct {
    const char *name;
    uint32_t duration_ms;
    const Action *actions;
    size_t action_count;
    int with_checksum; /* both hosts set host->checksum = enet_crc32 */
    uint32_t in_bw;    /* both hosts' incoming bandwidth (0 = unlimited) */
    uint32_t out_bw;   /* both hosts' outgoing bandwidth (0 = unlimited) */
} Scenario;

static const char *role_name(Role r) {
    switch (r) { case ROLE_C: return "C"; case ROLE_S: return "S"; case ROLE_D: return "D"; }
    return "?";
}

/* ---------------- payloads ---------------- */

static unsigned char payload_a[] = "hello-reliable-c2s";
static unsigned char payload_b[] = "hello-unreliable-c2s";
static unsigned char payload_c[] = "hello-unsequenced-c2s";
static unsigned char payload_d[] = "hello-reliable-s2c";
static unsigned char payload_e[] = "hello-unreliable-s2c";
static unsigned char payload_f[] = "hello-unsequenced-s2c";
static unsigned char payload_mtu[] = "just-under-mtu-payload-0123456789";

/* 40000-byte deterministic pattern for the fragmentation test */
static unsigned char payload_big[40000];
/* 8000-byte deterministic pattern for the unreliable-fragment test */
static unsigned char payload_unfrag[8000];
static int payloads_init_done = 0;
static void payloads_init(void) {
    if (payloads_init_done) return;
    for (size_t i = 0; i < sizeof payload_big; i++)
        payload_big[i] = (unsigned char)(i * 7 + (i >> 8));
    for (size_t i = 0; i < sizeof payload_unfrag; i++)
        payload_unfrag[i] = (unsigned char)(i * 13 + (i >> 6));
    payloads_init_done = 1;
}

/* ---------------- scenarios ---------------- */

static const Action act_connect[] = {
    { .at_ms = 5, .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
};

#define A_SEND(MS, R, CH, FL, BUF, LEN) \
    { .at_ms = (MS), .kind = ACT_SEND, .role = (R), .ch = (CH), \
      .flags = (FL), .data = (BUF), .data_len = (LEN) }
#define A_BCAST(MS, CH, FL, BUF, LEN) \
    { .at_ms = (MS), .kind = ACT_BROADCAST, .role = ROLE_S, .ch = (CH), \
      .flags = (FL), .data = (BUF), .data_len = (LEN) }
#define A_DISC(MS, R, DATA) \
    { .at_ms = (MS), .kind = ACT_DISCONNECT, .role = (R), .a = (DATA) }
#define A_DISCLATER(MS, R, DATA) \
    { .at_ms = (MS), .kind = ACT_DISCONNECT_LATER, .role = (R), .a = (DATA) }

static const Action act_send_c2s[] = {
    { .at_ms = 5,  .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    A_SEND(150, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_a, sizeof payload_a - 1),
    A_SEND(150, ROLE_C, 0, 0, payload_b, sizeof payload_b - 1),
    A_SEND(150, ROLE_C, 1, ENET_PACKET_FLAG_UNSEQUENCED, payload_c, sizeof payload_c - 1),
    A_SEND(160, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_mtu, sizeof payload_mtu - 1),
};

static const Action act_send_s2c[] = {
    { .at_ms = 5,  .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    A_SEND(150, ROLE_S, 0, ENET_PACKET_FLAG_RELIABLE, payload_d, sizeof payload_d - 1),
    A_SEND(150, ROLE_S, 0, 0, payload_e, sizeof payload_e - 1),
    A_SEND(150, ROLE_S, 1, ENET_PACKET_FLAG_UNSEQUENCED, payload_f, sizeof payload_f - 1),
};

static const Action act_frag[] = {
    { .at_ms = 5,   .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    A_SEND(150, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_big, sizeof payload_big),
};

static const Action act_disc_client[] = {
    { .at_ms = 5,   .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    A_SEND(150, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_a, sizeof payload_a - 1),
    A_DISC(250, ROLE_C, 42),
};

static const Action act_disc_server[] = {
    { .at_ms = 5,   .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    A_SEND(150, ROLE_S, 0, ENET_PACKET_FLAG_RELIABLE, payload_d, sizeof payload_d - 1),
    A_DISC(250, ROLE_S, 7),
};

static const Action act_idle[] = {
    { .at_ms = 5, .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
};

static const Action act_timeout[] = {
    { .at_ms = 5,   .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    /* server: fail fast: limit=4 attempts, min=200ms, max=600ms */
    { .at_ms = 100, .kind = ACT_PEER_TIMEOUT, .role = ROLE_S, .a = 4, .b = 200, .c = 600 },
    { .at_ms = 200, .kind = ACT_STOP_CLIENT,  .role = ROLE_C },
};

static const Action act_checksum[] = {
    { .at_ms = 5,  .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    A_SEND(150, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_a, sizeof payload_a - 1),
    A_SEND(150, ROLE_C, 0, 0, payload_b, sizeof payload_b - 1),
    A_SEND(160, ROLE_S, 0, ENET_PACKET_FLAG_RELIABLE, payload_d, sizeof payload_d - 1),
};

static const Action act_bandwidth[] = {
    { .at_ms = 5,  .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    A_SEND(150, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_a, sizeof payload_a - 1),
    A_SEND(150, ROLE_S, 0, ENET_PACKET_FLAG_RELIABLE, payload_d, sizeof payload_d - 1),
};

static const Action act_unfrag[] = {
    { .at_ms = 5,  .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    A_SEND(150, ROLE_C, 0, ENET_PACKET_FLAG_UNRELIABLE_FRAGMENT, payload_unfrag, sizeof payload_unfrag),
    A_SEND(160, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_a, sizeof payload_a - 1),
};

static const Action act_disclater[] = {
    { .at_ms = 5,   .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    A_SEND(150, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_a, sizeof payload_a - 1),
    A_SEND(150, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_mtu, sizeof payload_mtu - 1),
    A_DISCLATER(152, ROLE_C, 99),
};

static const Action act_multip[] = {
    { .at_ms = 5,  .kind = ACT_CONNECT, .role = ROLE_C, .a = 2, .b = 0 },
    { .at_ms = 5,  .kind = ACT_CONNECT, .role = ROLE_D, .a = 2, .b = 0 },
    A_SEND(150, ROLE_C, 0, ENET_PACKET_FLAG_RELIABLE, payload_a, sizeof payload_a - 1),
    A_SEND(150, ROLE_D, 0, ENET_PACKET_FLAG_RELIABLE, payload_d, sizeof payload_d - 1),
    A_BCAST(160, 1, ENET_PACKET_FLAG_RELIABLE, payload_c, sizeof payload_c - 1),
    A_SEND(170, ROLE_S, 0, ENET_PACKET_FLAG_RELIABLE, payload_f, sizeof payload_f - 1),
};

#define SC(NM, DUR, ACTS) \
    { .name = (NM), .duration_ms = (DUR), .actions = (ACTS), \
      .action_count = sizeof (ACTS) / sizeof ((ACTS)[0]), .with_checksum = 0, \
      .in_bw = 0, .out_bw = 0 }

#define SC_CS(NM, DUR, ACTS) \
    { .name = (NM), .duration_ms = (DUR), .actions = (ACTS), \
      .action_count = sizeof (ACTS) / sizeof ((ACTS)[0]), .with_checksum = 1, \
      .in_bw = 0, .out_bw = 0 }

#define SC_BW(NM, DUR, ACTS, IN, OUT) \
    { .name = (NM), .duration_ms = (DUR), .actions = (ACTS), \
      .action_count = sizeof (ACTS) / sizeof ((ACTS)[0]), .with_checksum = 0, \
      .in_bw = (IN), .out_bw = (OUT) }

static const Scenario scenarios[] = {
    SC("connect",      400,  act_connect),
    SC("send_c2s",     700,  act_send_c2s),
    SC("send_s2c",     700,  act_send_s2c),
    SC("frag",        1200,  act_frag),
    SC("disc_client",  800,  act_disc_client),
    SC("disc_server",  800,  act_disc_server),
    SC("idle",        2600,  act_idle),
    SC("timeout",     2200,  act_timeout),
    SC_CS("checksum",  700,  act_checksum),
    SC_BW("bandwidth", 2600, act_bandwidth, 1000000, 500000),
    SC("unfrag",       800,  act_unfrag),
    SC("disclater",    800,  act_disclater),
    SC("multip",       800,  act_multip),
};

/* ---------------- runner ---------------- */

static void make_addr(ENetAddress *addr, const char *ip, uint16_t port) {
    enet_address_set_host(addr, ip);
    addr->port = port;
}

static ENetHost *role_host(Role r, ENetHost *client, ENetHost *server, ENetHost *client2) {
    switch (r) {
    case ROLE_C: return client;
    case ROLE_S: return server;
    case ROLE_D: return client2;
    }
    return NULL;
}

static void perform_action(const Action *act, ENetHost *client, ENetHost *server, ENetHost *client2,
                           ENetPeer **client_peer, ENetPeer **server_peer, ENetPeer **client2_peer,
                           int *client_stopped) {
    ENetPeer *peer = NULL;
    Role r = act->role;

    switch (act->kind) {
    case ACT_CONNECT: {
        ENetAddress addr;
        uint16_t proxy_port = (r == ROLE_D) ? PROXY2_PORT : PROXY_PORT;
        make_addr(&addr, "127.0.0.1", proxy_port);
        ENetHost *host = role_host(r, client, server, client2);
        ENetPeer *p = enet_host_connect(host, &addr, act->a, act->b);
        if (p == NULL) { fprintf(stderr, "connect failed\n"); exit(1); }
        if (r == ROLE_C) *client_peer = p;
        if (r == ROLE_D) *client2_peer = p;
        fprintf(trace_file, "A %llu %s CONNECT host=127.0.0.1:%u channels=%u data=%u\n",
                (unsigned long long)now_ms(), role_name(r), proxy_port, act->a, act->b);
        return;
    }
    case ACT_SEND: {
        peer = (r == ROLE_C) ? *client_peer : (r == ROLE_D) ? *client2_peer : *server_peer;
        if (peer == NULL) return; /* not connected yet; skip silently */
        ENetPacket *pkt = enet_packet_create(act->data, act->data_len, act->flags);
        if (pkt == NULL) return;
        enet_peer_send(peer, (enet_uint8)act->ch, pkt);
        static char hex[2 * 1024 * 1024 + 1];
        hex_encode(act->data, act->data_len, hex);
        fprintf(trace_file, "A %llu %s SEND peer=%u ch=%u flags=%u hex=%s\n",
                (unsigned long long)now_ms(), role_name(r),
                peer->incomingPeerID, act->ch, act->flags, hex);
        return;
    }
    case ACT_BROADCAST: {
        static char hex[2 * 1024 * 1024 + 1];
        hex_encode(act->data, act->data_len, hex);
        fprintf(trace_file, "A %llu S BROADCAST ch=%u flags=%u hex=%s\n",
                (unsigned long long)now_ms(), act->ch, act->flags, hex);
        ENetPacket *pkt = enet_packet_create(act->data, act->data_len, act->flags);
        if (pkt == NULL) return;
        enet_host_broadcast(server, (enet_uint8)act->ch, pkt);
        return;
    }
    case ACT_DISCONNECT: {
        peer = (r == ROLE_C) ? *client_peer : (r == ROLE_D) ? *client2_peer : *server_peer;
        if (peer == NULL) return;
        fprintf(trace_file, "A %llu %s DISCONNECT peer=%u data=%u\n",
                (unsigned long long)now_ms(), role_name(r),
                peer->incomingPeerID, act->a);
        enet_peer_disconnect(peer, act->a);
        return;
    }
    case ACT_DISCONNECT_LATER: {
        peer = (r == ROLE_C) ? *client_peer : (r == ROLE_D) ? *client2_peer : *server_peer;
        if (peer == NULL) return;
        fprintf(trace_file, "A %llu %s DISCLATER peer=%u data=%u\n",
                (unsigned long long)now_ms(), role_name(r),
                peer->incomingPeerID, act->a);
        enet_peer_disconnect_later(peer, act->a);
        return;
    }
    case ACT_PEER_TIMEOUT: {
        peer = (r == ROLE_C) ? *client_peer : (r == ROLE_D) ? *client2_peer : *server_peer;
        if (peer == NULL) return;
        enet_peer_timeout(peer, act->a, act->b, act->c);
        fprintf(trace_file, "A %llu %s PEERTIMEOUT limit=%u min=%u max=%u\n",
                (unsigned long long)now_ms(), role_name(r), act->a, act->b, act->c);
        return;
    }
    case ACT_STOP_CLIENT: {
        *client_stopped = 1;
        fprintf(trace_file, "A %llu C STOP\n", (unsigned long long)now_ms());
        return;
    }
    }
}

static void run_scenario(const Scenario *sc) {
    ENetAddress client_addr_en, client2_addr_en, server_addr_en;
    make_addr(&client_addr_en, "127.0.0.1", CLIENT_PORT);
    make_addr(&client2_addr_en, "127.0.0.1", CLIENT2_PORT);
    make_addr(&server_addr_en, "127.0.0.1", SERVER_PORT);

    ENetHost *client = enet_host_create(&client_addr_en, 1, 2, sc->in_bw, sc->out_bw);
    ENetHost *server = enet_host_create(&server_addr_en, 16, 2, sc->in_bw, sc->out_bw);
    ENetHost *client2 = enet_host_create(&client2_addr_en, 1, 2, sc->in_bw, sc->out_bw);
    if (!client || !server || !client2) { fprintf(stderr, "host create failed\n"); exit(1); }
    if (sc->with_checksum) {
        client->checksum = enet_crc32;
        server->checksum = enet_crc32;
    }

    ENetPeer *client_peer = NULL, *server_peer = NULL, *client2_peer = NULL;
    char done[64] = {0};
    int client_stopped = 0;

    proxy_init();

    uint64_t t;
    while ((t = now_ms()) < sc->duration_ms) {
        for (size_t i = 0; i < sc->action_count; i++) {
            if (!done[i] && sc->actions[i].at_ms <= t) {
                perform_action(&sc->actions[i], client, server, client2,
                               &client_peer, &server_peer, &client2_peer, &client_stopped);
                done[i] = 1;
            }
        }
        if (!client_stopped) drain_events(client, "C", &client_peer);
        drain_events(server, "S", &server_peer);
        drain_events(client2, "D", &client2_peer);
        proxy_pump();
        usleep(500);
    }

    close(proxy_fd);
    close(proxy2_fd);
    enet_host_destroy(client);
    enet_host_destroy(server);
    enet_host_destroy(client2);
}

/* ---------------- main ---------------- */

static void hex_decode(const char *hex, unsigned char *out, size_t len) {
    for (size_t i = 0; i < len; i++)
        if (sscanf(hex + 2 * i, "%2hhx", &out[i]) != 1) exit(1);
}

int main(int argc, char **argv) {
    if (argc != 3 || strcmp(argv[1], "record") != 0) {
        fprintf(stderr, "usage: harness record <scenario>\n"
                        "scenarios: connect send_c2s send_s2c frag "
                        "disc_client disc_server idle timeout checksum "
                        "bandwidth unfrag disclater multip\n");
        return 1;
    }
    const char *want = argv[2];

    if (enet_initialize() != 0) {
        fprintf(stderr, "enet_initialize failed\n");
        return 1;
    }
    payloads_init();

    char path[256];
    snprintf(path, sizeof path, "traces/%s.trace", want);
    trace_file = fopen(path, "w");
    if (trace_file == NULL) { perror("fopen"); return 1; }

    /* fixed script seed so traces are reproducible run-to-run */
    enet_time_set(0);
    clock_gettime(CLOCK_MONOTONIC, &t_start);

    fprintf(trace_file, "V lenet-trace-1\n");

    const Scenario *found = NULL;
    for (size_t i = 0; i < sizeof scenarios / sizeof scenarios[0]; i++)
        if (strcmp(scenarios[i].name, want) == 0) found = &scenarios[i];
    if (found == NULL) {
        fprintf(stderr, "unknown scenario: %s\n", want);
        return 1;
    }

    fprintf(trace_file, "S %s\n", found->name);
    run_scenario(found);
    fclose(trace_file);
    enet_deinitialize();
    printf("recorded %s\n", path);
    return 0;
}
