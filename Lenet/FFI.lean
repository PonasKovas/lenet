import Lenet.Host

/-!
# C exports

The `lenet_ffi_*` symbols wrapped by `csrc/lenet_capi.c` into the public C
API (`csrc/include/lenet.h`). A C host handle is an `IO.Ref HostContext`;
events and datagrams queue up in the context until the driver polls them.

Every update goes through `IO.Ref.modify`/`modifyGet`, which take the value
out of the reference while the function runs: the host stays uniquely
referenced, so Lean updates it in place instead of copying it on every call.
-/

namespace Lenet.FFI

structure HostContext where
  host           : Host
  pendingEvents  : Std.Queue Event := .empty
  pendingPackets : Std.Queue (Address × ByteArray) := .empty

abbrev HostRef := IO.Ref HostContext

/-- Appends `xs` to `q` in order (`Std.Queue.enqueueAll` expects them
newest first). -/
@[inline] def enqueueAll (q : Std.Queue α) (xs : Array α) : Std.Queue α :=
  xs.foldl (fun q x => q.enqueue x) q

/-- Runs a host update on the context. -/
@[inline] def modifyHost (ctx : HostRef) (f : Host → Host) : IO Unit :=
  ctx.modify fun c => { c with host := f c.host }

/-- Runs a fallible host update: on error the host is left unchanged. -/
@[inline] def tryModifyHost (ctx : HostRef) (f : Host → Except LenetError (Host × α)) :
    IO (Option α) :=
  ctx.modifyGet fun c =>
    match f c.host with
    | .ok (host, a) => (some a, { c with host })
    | .error _ => (none, c)

@[export lenet_ffi_host_create]
def hostCreate (hostIp : UInt32) (port : UInt16) (peerCount channelLimit : USize)
    (inBw outBw seed mtu : UInt32) : IO HostRef :=
  IO.mkRef { host := Host.create { host := hostIp, port } peerCount.toNat channelLimit.toNat inBw outBw seed mtu }

/-- Nothing to do: the export consumes the handle's last reference. -/
@[export lenet_ffi_host_destroy]
def hostDestroy (_ctx : HostRef) : IO Unit :=
  pure ()

/-- The new peer ID, or -1 when no slot is free. -/
@[export lenet_ffi_host_connect]
def hostConnect (ctx : HostRef) (ip : UInt32) (port : UInt16) (channelCount : USize) (data : UInt32) :
    IO Int32 := do
  let peerId ← tryModifyHost ctx (·.connect { host := ip, port } channelCount.toNat data)
  return peerId.map (·.toNat.toInt32) |>.getD (-1)

/-- 0 on success, -1 on error. -/
@[export lenet_ffi_host_send]
def hostSend (ctx : HostRef) (peerId : UInt16) (channelId : UInt8) (flags : UInt32) (data : ByteArray) :
    IO Int32 := do
  let packet : Packet := { data, delivery := DeliveryMode.fromFlags flags }
  -- `trySend` hands the host back even on error, so the context is never
  -- held twice and the host updates in place
  let sent ← ctx.modifyGet fun c =>
    let (host, result) := c.host.trySend peerId channelId packet
    (result, { c with host })
  return if sent matches .ok () then 0 else -1

@[export lenet_ffi_host_broadcast]
def hostBroadcast (ctx : HostRef) (channelId : UInt8) (flags : UInt32) (data : ByteArray) : IO Unit :=
  modifyHost ctx (·.broadcast channelId { data, delivery := DeliveryMode.fromFlags flags })

@[export lenet_ffi_host_disconnect]
def hostDisconnect (ctx : HostRef) (peerId : UInt16) (data : UInt32) : IO Unit :=
  modifyHost ctx (·.disconnect peerId data)

@[export lenet_ffi_host_disconnect_later]
def hostDisconnectLater (ctx : HostRef) (peerId : UInt16) (data : UInt32) : IO Unit :=
  modifyHost ctx (·.disconnectLater peerId data)

@[export lenet_ffi_host_enable_checksum]
def hostEnableChecksum (ctx : HostRef) : IO Unit :=
  modifyHost ctx ({ · with checksumEnabled := true })

@[export lenet_ffi_peer_throttle_configure]
def peerThrottleConfigure (ctx : HostRef) (peerId : UInt16) (interval accel decel : UInt32) : IO Unit :=
  modifyHost ctx (·.throttleConfigure peerId interval accel decel)

@[export lenet_ffi_set_peer_timeout]
def peerSetTimeout (ctx : HostRef) (peerId : UInt16) (limit minimum maximum : UInt32) : IO Unit :=
  modifyHost ctx (·.setPeerTimeout peerId limit minimum maximum)

@[export lenet_ffi_host_handle_datagram]
def hostHandleDatagram (ctx : HostRef) (now ip : UInt32) (port : UInt16) (data : ByteArray) : IO Unit :=
  ctx.modify fun c =>
    let (host, events) := c.host.handleDatagram now { host := ip, port } data
    { c with host, pendingEvents := enqueueAll c.pendingEvents events }

@[export lenet_ffi_host_service]
def hostService (ctx : HostRef) (now : UInt32) : IO Unit :=
  ctx.modify fun c =>
    let (host, datagrams, events) := c.host.service now
    { host
      pendingPackets := enqueueAll c.pendingPackets datagrams
      pendingEvents  := enqueueAll c.pendingEvents events }

@[export lenet_ffi_host_next_deadline]
def hostNextDeadline (ctx : HostRef) : IO (Option UInt32) :=
  return (← ctx.get).host.nextDeadline

/-- The oldest pending event as `(type, peer, channel, data, payload)`, with
the `LENET_EVENT_*` type codes of `lenet.h`. -/
@[export lenet_ffi_host_poll_event]
def hostPollEvent (ctx : HostRef) : IO (Option (UInt32 × UInt16 × UInt8 × UInt32 × ByteArray)) :=
  ctx.modifyGet fun c =>
    match c.pendingEvents.dequeue? with
    | none => (none, c)
    | some (event, rest) =>
      let row := match event with
        | .connect peerId data => (1, peerId, 0, data, .empty)
        | .disconnect peerId data => (2, peerId, 0, data, .empty)
        | .receive peerId channelId packet => (3, peerId, channelId, 0, packet.data)
      (some row, { c with pendingEvents := rest })

/-- The oldest pending datagram as `(ip, port, bytes)`. -/
@[export lenet_ffi_host_poll_outgoing]
def hostPollOutgoing (ctx : HostRef) : IO (Option (UInt32 × UInt16 × ByteArray)) :=
  ctx.modifyGet fun c =>
    match c.pendingPackets.dequeue? with
    | none => (none, c)
    | some ((addr, bytes), rest) => (some (addr.host, addr.port, bytes), { c with pendingPackets := rest })

end Lenet.FFI
