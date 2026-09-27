# Differences from ENet

Lenet is compatible with ENet 1.3.x on the wire (tested against
1.3.18-17, `5a9c537`). It follows ENet's behavior closely, except in the
places below. None of them breaks talking to an ENet host.

## Bugs in ENet that Lenet does not copy

- **An ACK can lose a reliable packet.** ENet acknowledges a reliable
  command that it drops for being one window past its receive window. An
  ENet sender can be that far ahead (up to seven windows in flight). If the
  first command of a window is lost while the sender moves on six more
  windows, the command that opens the seventh is acknowledged but never
  delivered, and the channel stalls for good. Lenet fixes both ends: as a
  receiver it does not acknowledge such a command, and as a sender it keeps
  at most six windows in flight.
- **Bandwidth throttle overflow.** ENet computes `bandwidth * elapsed` in
  32 bits, which wraps once a bandwidth passes about 4.3 MB/s, and
  subtracts from a host budget that can go below zero and wrap to "no
  limit". Lenet does not wrap.
- **One dropped unsequenced packet drops the ones behind it.** When the
  packet throttle drops a packet, ENet also drops every following command
  with the same sequence numbers (meant for the rest of a fragment set).
  All unsequenced packets share (0, 0), so they all go. Lenet drops only
  the packet the throttle picked.
- **Datagrams over the MTU with checksums on.** ENet does not count the
  4-byte checksum when packing, so a datagram can be MTU + 4 bytes. Lenet
  counts it.
- **Unsequenced packets stuck behind unreliable ones.** ENet queues an
  unsequenced packet with the channel's unreliable packets, so it waits
  behind one held for a missing reliable packet, possibly forever. Where it
  lands depends on the receive frontier, because the insertion loop tests
  the new command's type where it means the queued one's. Lenet delivers
  an unsequenced packet when it arrives.
- **Stale packets stall the channel.** A hostile sender can send a
  reliable packet numbered inside a fragment set's span before the set.
  ENet keeps it at the head of its queue, where it blocks delivery until
  the sequence numbers wrap. Lenet drops what the set jumps over.
- **A full receive budget stalls the channel.** Once a peer holds 32 MB of
  undelivered data, ENet refuses every new packet, including the one the
  channel needs next to deliver what it holds, so the connection stalls
  until it times out. Lenet always takes that next packet.
- **Fragment memory.** ENet allocates the whole packet (up to 32 MB) when
  the first fragment of a set arrives, and completes a set once enough
  fragments arrived, whatever their sizes. So one 1-byte fragment costs
  32 MB. Lenet stores only the bytes that arrived and completes a set only
  when they add up to its length.

## Other differences

These are choices, not fixes. They change timing or what happens with
reordered or hostile traffic, never what an honest ENet peer sees go wrong.

- **Compression** is not supported. Compressed datagrams are dropped.
- **Unsequenced duplicate window.** ENet tracks groups in aligned blocks
  of 1024 and drops everything below the current block, seen or not, so
  when group 1024 overtakes 1023, ENet drops 1023. Lenet keeps a window of
  1024 groups sliding behind the highest one and delivers any group it has
  not seen.
- **Retransmit timing.** ENet checks for timed-out commands only once the
  front command's deadline passes. Lenet checks each command against its
  own deadline, so it may resend one sooner.
- **A timeout does not end the send pass.** When a peer times out, ENet
  stops sending for that service call. Lenet serves the other peers too.
- **Resource caps.** Lenet allows 32 fragment sets in progress per peer
  (a new set evicts the oldest unreliable one; a reliable fragment that
  finds no room is not acknowledged, so it gets resent) and 1024 held-back
  unreliable packets per channel. ENet caps these only through its byte
  budget.
- **The byte budget** counts what the channels hold back and the fragment
  sets in progress. ENet also counts packets delivered but not yet read by
  the application. Lenet hands those out as events.
- **Late unreliable fragment sets.** ENet delivers an unreliable fragment
  set that completes after newer packets on its channel, and moves the
  channel's counter back. Lenet drops it.
- **A fragment set starting at a delivered or held packet.** ENet refuses
  it. Lenet acknowledges and ignores it.
- **UNSEQUENCED together with UNRELIABLE_FRAGMENT** (C API). ENet sends a
  large packet with both flags as unreliable fragments. Lenet sends it as
  reliable fragments, as with UNSEQUENCED alone.
- **A PING that does not fit.** ENet sends a keepalive PING only if it
  fits the current datagram. Lenet sends it in the next one.
