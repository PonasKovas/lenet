#ifndef LENET_H
#define LENET_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/** Opaque handle to a sans-I/O Lenet host instance. */
typedef struct LeNetHost LeNetHost;

/** Event types emitted by the protocol engine. */
typedef enum LeNetEventType {
    LENET_EVENT_TYPE_NONE       = 0,
    LENET_EVENT_TYPE_CONNECT    = 1,
    LENET_EVENT_TYPE_DISCONNECT = 2,
    LENET_EVENT_TYPE_RECEIVE    = 3
} LeNetEventType;

/** High-level application event. */
typedef struct LeNetEvent {
    LeNetEventType type;
    uint16_t       peer_id;
    uint8_t        channel_id;
    uint32_t       data;
    const uint8_t* packet_data;
    size_t         packet_len;
} LeNetEvent;

/** Outgoing datagram to be transmitted over UDP socket. */
typedef struct LeNetOutgoingPacket {
    uint32_t       dest_ip;
    uint16_t       dest_port;
    const uint8_t* data;
    size_t         data_len;
} LeNetOutgoingPacket;

/** Delivery reliability flags. */
typedef enum LeNetDeliveryMode {
    LENET_DELIVERY_UNRELIABLE          = 0,
    LENET_DELIVERY_RELIABLE            = (1 << 0),
    LENET_DELIVERY_UNSEQUENCED         = (1 << 1),
    LENET_DELIVERY_UNRELIABLE_FRAGMENT = (1 << 3)
} LeNetDeliveryMode;

/* --- Host Lifecycle --- */

/**
 * Creates a sans-I/O host instance.
 * @param host_ip Local binding IP (network byte order).
 * @param port Local binding port.
 * @param peer_count Maximum simultaneous peer slots.
 * @param channel_limit Maximum channels allowed per peer.
 * @param in_bandwidth Downstream bandwidth limit (0 = unlimited).
 * @param out_bandwidth Upstream bandwidth limit (0 = unlimited).
 * @param seed Random seed for connectId generation.
 */
LeNetHost* lenet_host_create(
    uint32_t host_ip,
    uint16_t port,
    size_t   peer_count,
    size_t   channel_limit,
    uint32_t in_bandwidth,
    uint32_t out_bandwidth,
    uint32_t seed
);

/** Destroys a host instance and frees all internal memory. */
void lenet_host_destroy(LeNetHost* host);

/* --- Connection Management & Sending --- */

/**
 * Initiates an outgoing connection to a remote host.
 * @return Allocated peer ID (>= 0) on success, or negative on error.
 */
int32_t lenet_host_connect(
    LeNetHost* host,
    uint32_t   dest_ip,
    uint16_t   dest_port,
    size_t     channel_count,
    uint32_t   data
);

/** Queues a packet for transmission to a connected peer. */
int32_t lenet_host_send(
    LeNetHost*     host,
    uint16_t       peer_id,
    uint8_t        channel_id,
    uint32_t       delivery_mode,
    const uint8_t* data,
    size_t         len
);

/** Broadcasts a packet to all connected peers. */
void lenet_host_broadcast(
    LeNetHost*     host,
    uint8_t        channel_id,
    uint32_t       delivery_mode,
    const uint8_t* data,
    size_t         len
);

/** Disconnects a peer. */
void lenet_host_disconnect(LeNetHost* host, uint16_t peer_id, uint32_t data);

/* --- Sans-I/O Ingest & Service --- */

/**
 * Feeds an incoming UDP datagram received from the socket into the protocol engine.
 */
int32_t lenet_host_handle_datagram(
    LeNetHost*     host,
    uint32_t       now_ms,
    uint32_t       src_ip,
    uint16_t       src_port,
    const uint8_t* data,
    size_t         len
);

/**
 * Drives periodic maintenance (timeouts, retransmissions, pings, bandwidth throttle).
 */
int32_t lenet_host_service(LeNetHost* host, uint32_t now_ms);

/* --- Polling Outputs --- */

/**
 * Polls the next queued application event.
 * @return 1 if an event was returned in `out_event`, 0 if queue is empty.
 */
int32_t lenet_host_poll_event(LeNetHost* host, LeNetEvent* out_event);

/**
 * Polls the next outgoing UDP packet to be sent over the network.
 * @return 1 if a packet was returned in `out_packet`, 0 if queue is empty.
 */
int32_t lenet_host_poll_outgoing(LeNetHost* host, LeNetOutgoingPacket* out_packet);

#ifdef __cplusplus
}
#endif

#endif /* LENET_H */