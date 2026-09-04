import Lenet.Constants
import Lenet.Address
import Lenet.Packet
import Lenet.Event
import Lenet.Host

namespace Lenet.FFI

/--
Internal state container for an FFI-managed sans-I/O host instance.
Buffers emitted events and outgoing datagrams for polling by C/Rust callers.
-/
structure HostContext where
  host           : Host
  pendingEvents  : Array Event := #[]
  pendingPackets : Array (Address × ByteArray) := #[]
  activePacket   : ByteArray := ByteArray.empty
  activeEventPkt : ByteArray := ByteArray.empty

@[export lenet_ffi_host_create]
def ffi_host_create (hostIp : UInt32) (port : UInt16) (peerCount : USize) (channelLimit : USize) (inBw : UInt32) (outBw : UInt32) (seed : UInt32) : IO (Option (IO.Ref HostContext)) := do
  let address : Address := { host := hostIp, port }
  let host := Host.create address peerCount.toNat channelLimit.toNat inBw outBw seed
  let ctx ← IO.mkRef { host := host }
  return some ctx

@[export lenet_ffi_host_destroy]
def ffi_host_destroy (_ctxRef : IO.Ref HostContext) : IO Unit := do
  pure ()

@[export lenet_ffi_host_connect]
def ffi_host_connect (ctxRef : IO.Ref HostContext) (destIp : UInt32) (destPort : UInt16) (channelCount : USize) (data : UInt32) : IO Int32 := do
  let ctx ← ctxRef.get
  match ctx.host.connect { host := destIp, port := destPort } channelCount.toNat data with
  | .ok (newHost, peerId) =>
    ctxRef.set { ctx with host := newHost }
    return peerId.toNat.toInt32
  | .error _ =>
    return -1

@[export lenet_ffi_host_send]
def ffi_host_send (ctxRef : IO.Ref HostContext) (peerId : UInt16) (channelId : UInt8) (mode : UInt32) (data : ByteArray) : IO Int32 := do
  let ctx ← ctxRef.get
  let delivery := DeliveryMode.fromFlags mode
  let pkt : Packet := { data := data, delivery }
  match ctx.host.send peerId channelId pkt with
  | .ok newHost =>
    ctxRef.set { ctx with host := newHost }
    return 0
  | .error _ =>
    return -1

@[export lenet_ffi_host_broadcast]
def ffi_host_broadcast (ctxRef : IO.Ref HostContext) (channelId : UInt8) (mode : UInt32) (data : ByteArray) : IO Unit := do
  let ctx ← ctxRef.get
  let delivery := DeliveryMode.fromFlags mode
  let pkt : Packet := { data := data, delivery }
  let newHost := ctx.host.broadcast channelId pkt
  ctxRef.set { ctx with host := newHost }

@[export lenet_ffi_host_disconnect]
def ffi_host_disconnect (ctxRef : IO.Ref HostContext) (peerId : UInt16) (data : UInt32) : IO Unit := do
  let ctx ← ctxRef.get
  let newHost := ctx.host.disconnect peerId data
  ctxRef.set { ctx with host := newHost }

@[export lenet_ffi_set_peer_timeout]
def ffi_set_peer_timeout (ctxRef : IO.Ref HostContext) (peerId : UInt16) (limit mn mx : UInt32) : IO Unit := do
  let ctx ← ctxRef.get
  let idx := peerId.toNat
  if h : idx < ctx.host.peers.size then
    let p := ctx.host.peers[idx]
    let p' := { p with timeoutLimit := limit, timeoutMinimum := mn, timeoutMaximum := mx }
    ctxRef.set { ctx with host := { ctx.host with peers := ctx.host.peers.set idx p' h } }

@[export lenet_ffi_host_handle_datagram]
def ffi_host_handle_datagram (ctxRef : IO.Ref HostContext) (nowMs : UInt32) (srcIp : UInt32) (srcPort : UInt16) (data : ByteArray) : IO Int32 := do
  let ctx ← ctxRef.get
  let (newHost, events) := ctx.host.handleDatagram nowMs { host := srcIp, port := srcPort } data
  ctxRef.set { ctx with
    host          := newHost
    pendingEvents := ctx.pendingEvents ++ events
  }
  return 0

@[export lenet_ffi_host_service]
def ffi_host_service (ctxRef : IO.Ref HostContext) (nowMs : UInt32) : IO Int32 := do
  let ctx ← ctxRef.get
  let (newHost, outgoing, events) := ctx.host.service nowMs
  ctxRef.set { ctx with
    host           := newHost
    pendingPackets := ctx.pendingPackets ++ outgoing
    pendingEvents  := ctx.pendingEvents ++ events
  }
  return 0

@[export lenet_ffi_host_poll_event]
def ffi_host_poll_event (ctxRef : IO.Ref HostContext) : IO (Option (UInt32 × UInt16 × UInt8 × UInt32 × ByteArray)) := do
  let ctx ← ctxRef.get
  if ctx.pendingEvents.isEmpty then
    return none
  else
    let ev := ctx.pendingEvents[0]!
    let remainingEvents := if h : 0 < ctx.pendingEvents.size then ctx.pendingEvents.eraseIdx 0 h else #[]
    ctxRef.set { ctx with pendingEvents := remainingEvents }
    match ev with
    | .connect peerId data =>
      return some (1, peerId, 0, data, ByteArray.empty)
    | .disconnect peerId data =>
      return some (2, peerId, 0, data, ByteArray.empty)
    | .receive peerId channelId packet =>
      return some (3, peerId, channelId, 0, packet.data)

@[export lenet_ffi_host_poll_outgoing]
def ffi_host_poll_outgoing (ctxRef : IO.Ref HostContext) : IO (Option (UInt32 × UInt16 × ByteArray)) := do
  let ctx ← ctxRef.get
  if ctx.pendingPackets.isEmpty then
    return none
  else
    let (addr, bytes) := ctx.pendingPackets[0]!
    let remainingPackets := if h : 0 < ctx.pendingPackets.size then ctx.pendingPackets.eraseIdx 0 h else #[]
    ctxRef.set { ctx with pendingPackets := remainingPackets }
    return some (addr.host, addr.port, bytes)

end Lenet.FFI