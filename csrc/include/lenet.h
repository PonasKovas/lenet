/*
 * Lenet public C API.
 *
 * Lenet is a sans-I/O implementation of the ENet protocol: it never opens
 * sockets or reads clocks. The application owns a UDP socket and the clock
 * and drives the host through this API:
 *
 *   - feed every received UDP datagram in with lenet_host_handle_datagram,
 *   - call lenet_host_service(now_ms) periodically (every event-loop tick),
 *   - transmit every datagram returned by lenet_host_poll_outgoing,
 *   - consume application events with lenet_host_poll_event.
 *
 * This makes the API usable directly from C, or wrapped for sync or async
 * runtimes (e.g. Rust/Tokio): every call is non-blocking and time is
 * always supplied by the caller.
 *
 * Driver rules:
 *   - Datagrams (ACKs included) are only produced by lenet_host_service:
 *     call it after feeding datagrams, then drain lenet_host_poll_outgoing.
 *   - Between datagrams, servicing at lenet_host_next_deadline is enough;
 *     there is no need to busy-poll.
 *   - Times are milliseconds on any monotonic clock, truncated to 32 bits.
 *     They may wrap; compare them wrap-aware.
 *   - On the server side the CONNECT event fires when the client
 *     acknowledges the handshake, not when its CONNECT arrives.
 *
 * Threading: a lenet_host is NOT thread-safe. Drive each host from a
 * single thread (or serialize access with your own lock).
 */
#ifndef LENET_H
#define LENET_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/** Opaque host instance. Invalid after lenet_host_destroy. */
typedef struct lenet_host lenet_host;

/** Packet delivery modes (bitmask, ENet-compatible). */
enum {
    LENET_UNRELIABLE          = 0,
    LENET_RELIABLE            = (1 << 0),
    LENET_UNSEQUENCED         = (1 << 1),
    LENET_UNRELIABLE_FRAGMENT = (1 << 3)
};

/** Event types. */
enum {
    LENET_EVENT_NONE       = 0,
    LENET_EVENT_CONNECT    = 1,
    LENET_EVENT_DISCONNECT = 2,
    LENET_EVENT_RECEIVE    = 3
};

/** Application event. For LENET_EVENT_RECEIVE the payload is delivered
 * separately by lenet_host_poll_event's output buffer. */
typedef struct {
    uint32_t type;       /* LENET_EVENT_* */
    uint16_t peer_id;
    uint8_t  channel_id;
    uint32_t data;
} lenet_event;

/** Peer states, numbered as ENet's ENetPeerState (Lenet has no
 * CONNECTION_PENDING = 3 or CONNECTION_SUCCEEDED = 4). */
enum {
    LENET_PEER_STATE_DISCONNECTED            = 0,
    LENET_PEER_STATE_CONNECTING              = 1,
    LENET_PEER_STATE_ACKNOWLEDGING_CONNECT   = 2,
    LENET_PEER_STATE_CONNECTED               = 5,
    LENET_PEER_STATE_DISCONNECT_LATER        = 6,
    LENET_PEER_STATE_DISCONNECTING           = 7,
    LENET_PEER_STATE_ACKNOWLEDGING_DISCONNECT = 8,
    LENET_PEER_STATE_ZOMBIE                  = 9
};

/** A peer as the application may inspect it. `ip` is in network byte
 * order, `port` in host byte order; times in ms; the packet throttle is
 * out of 32 (ENet's ENET_PEER_PACKET_THROTTLE_SCALE). */
typedef struct {
    uint32_t state;                    /* LENET_PEER_STATE_* */
    uint32_t ip;
    uint16_t port;
    uint32_t round_trip_time;
    uint32_t round_trip_time_variance;
    uint32_t packet_throttle;
} lenet_peer_info;

/** Outgoing datagram to transmit over the driver's UDP socket.
 * `ip` is in network byte order, `port` in host byte order.
 * `data` points to an internal buffer that is valid until the next
 * lenet_host_poll_outgoing call. */
typedef struct {
    uint32_t    ip;
    uint16_t    port;
    const void *data;
    size_t      len;
} lenet_datagram;

/*
 * Initializes the library runtime. Optional: every entry point performs
 * lazy one-time initialization; this function exists so embedders can
 * pay the cost up front. Idempotent.
 */
void lenet_initialize(void);

/*
 * Creates a host. bind_ip/bind_port are informational (the socket is the
 * driver's); incoming_bw/outgoing_bw are bytes/second, 0 = unlimited;
 * mtu is clamped to [576, 4096] (0 = default 1392).
 * Returns NULL on failure, and when peer_count exceeds 4095 (as ENet).
 */
lenet_host *lenet_host_create(uint32_t bind_ip, uint16_t bind_port,
                              size_t peer_count, size_t channel_limit,
                              uint32_t incoming_bw, uint32_t outgoing_bw,
                              uint32_t mtu);

/** Destroys a host and frees all resources associated with it. */
void lenet_host_destroy(lenet_host *host);

/**
 * Starts a connection attempt to `ip:port` with `channel_count` channels
 * (1..255) and `user_data` as the connect payload.
 * Returns the local peer id (>= 0), or -1 if no peer slot is free.
 */
int32_t lenet_host_connect(lenet_host *host, uint32_t ip, uint16_t port,
                           size_t channel_count, uint32_t user_data);

/**
 * Queues a packet for transmission on `channel`. `flags` is one
 * LENET_* delivery mode.
 * Returns 0 on success, -1 on error (unknown peer, peer not connected,
 * channel out of range, packet too large).
 */
int32_t lenet_host_send(lenet_host *host, uint16_t peer_id, uint8_t channel,
                        uint32_t flags, const void *data, size_t len);

/** Queues a packet on `channel` of every connected peer. */
void lenet_host_broadcast(lenet_host *host, uint8_t channel, uint32_t flags,
                          const void *data, size_t len);

/** Begins a graceful disconnect of `peer_id`. */
void lenet_host_disconnect(lenet_host *host, uint16_t peer_id, uint32_t data);

/** ENet's enet_peer_disconnect_later: flushes queued packets, then
 * disconnects. Degrades to lenet_host_disconnect when nothing is pending. */
void lenet_host_disconnect_later(lenet_host *host, uint16_t peer_id, uint32_t data);

/** ENet's enet_peer_disconnect_now: ends the connection at once, without a
 * DISCONNECT event. A connection still up sends one unacknowledged
 * DISCONNECT on the next service or flush; the slot is free after it. */
void lenet_peer_disconnect_now(lenet_host *host, uint16_t peer_id, uint32_t data);

/** ENet's enet_peer_reset: frees the slot at once; nothing is sent and no
 * event is reported. */
void lenet_peer_reset(lenet_host *host, uint16_t peer_id);

/** ENet's enet_peer_ping: queues a PING to a connected peer. */
void lenet_peer_ping(lenet_host *host, uint16_t peer_id);

/** ENet's enet_peer_ping_interval: how long a peer may be idle before the
 * keepalive PING, in ms; 0 means the default (500). */
void lenet_peer_ping_interval(lenet_host *host, uint16_t peer_id, uint32_t interval_ms);

/** ENet's enet_host_bandwidth_limit: new bandwidths in bytes/second,
 * 0 = unlimited; peers learn their new limits at the next throttle epoch. */
void lenet_host_bandwidth_limit(lenet_host *host, uint32_t incoming_bw, uint32_t outgoing_bw);

/** ENet's enet_host_channel_limit: the most channels an incoming
 * connection gets; 0 means 255. */
void lenet_host_channel_limit(lenet_host *host, size_t channel_limit);

/** Fills *out with peer `peer_id`'s state, address, RTT and packet
 * throttle. Returns 0, or -1 for an unknown peer ID. */
int32_t lenet_peer_get_info(lenet_host *host, uint16_t peer_id, lenet_peer_info *out);

/** ENet's enet_peer_throttle_configure: sets the local throttle parameters
 * and informs the remote peer. */
void lenet_peer_throttle_configure(lenet_host *host, uint16_t peer_id,
                                   uint32_t interval, uint32_t acceleration,
                                   uint32_t deceleration);

/** Enables CRC32 checksums (must be enabled on both ends, like ENet's
 * host->checksum = enet_crc32). Datagrams without a valid checksum are
 * dropped on receive; all emitted datagrams carry one. */
void lenet_host_enable_checksum(lenet_host *host);

/** Configures timeout behavior for `peer_id` (see enet_peer_timeout); 0 keeps
 * that parameter's default. */
void lenet_peer_set_timeout(lenet_host *host, uint16_t peer_id,
                            uint32_t limit, uint32_t minimum, uint32_t maximum);

/**
 * Feeds one received UDP datagram into the protocol engine.
 * `ip` (network byte order) and `port` (host byte order) identify the
 * sender. Returns 0 on success (the datagram was consumed; it may still
 * have been discarded as invalid), -1 on error.
 */
int32_t lenet_host_handle_datagram(lenet_host *host, uint32_t now_ms,
                                   uint32_t ip, uint16_t port,
                                   const void *data, size_t len);

/**
 * ENet's enet_host_flush: packs everything queued into datagrams (poll
 * them with lenet_host_poll_outgoing) without running the timers.
 * Returns 0 on success, -1 on error.
 */
int32_t lenet_host_flush(lenet_host *host, uint32_t now_ms);

/**
 * Runs the connection's timers: retransmissions, timeouts, keepalive
 * pings, and the periodic bandwidth recalculation. Call this regularly,
 * at least a few times per second. Returns 0 on success, -1 on error.
 */
int32_t lenet_host_service(lenet_host *host, uint32_t now_ms);

/**
 * Returns 1 and stores the next wall-clock deadline (ms, same clock as
 * service) at which the host's state can change in *deadline, 0 if
 * nothing is scheduled, -1 on error. Drivers use this to schedule their
 * next service tick without busy-pumping. Timestamps may wrap; compare
 * wrap-aware.
 */
int32_t lenet_host_next_deadline(lenet_host *host, uint32_t *deadline);

/**
 * Pops one application event into *out.
 * For LENET_EVENT_RECEIVE, up to payload_cap bytes of the packet payload
 * are copied into payload_buf (may be NULL to learn the size only) and
 * *payload_len is set to the full payload length; if *payload_len exceeds
 * the number of bytes copied the payload was truncated.
 * Returns 1 if an event was returned, 0 if none is pending, -1 on error.
 */
int32_t lenet_host_poll_event(lenet_host *host, lenet_event *out,
                              void *payload_buf, size_t payload_cap,
                              size_t *payload_len);

/**
 * Pops one outgoing datagram into *out. Returns 1 if there is one,
 * 0 if none is pending, -1 on error. out->data points to an internal
 * buffer valid until the next lenet_host_poll_outgoing call.
 */
int32_t lenet_host_poll_outgoing(lenet_host *host, lenet_datagram *out);

#ifdef __cplusplus
}
#endif

#endif /* LENET_H */
