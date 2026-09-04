namespace Lenet

/--
Typed errors surfaced by the fallible API calls (`Host.connect`, `Host.send`,
`Peer.send`). One constructor per failure mode; the C API maps any of these to
a generic failure code, Lean callers can pattern-match.
-/
inductive LenetError where
  /-- `Host.connect` with no disconnected slot available to reuse. -/
  | noFreePeerSlots
  /-- `Host.send` addressed a peer slot beyond the host's peer count. -/
  | invalidPeerId (peerId : UInt16)
  /-- `Peer.send` on a peer that is not in the connected state. -/
  | peerNotConnected (peerId : UInt16)
  /-- `Peer.send` on a channel the peer does not have. -/
  | invalidChannelId (peerId : UInt16) (channelId : UInt8) (channelCount : Nat)
  /-- `Peer.send` of a packet whose payload would need more than
  `Constants.maximumFragmentCount` fragments. -/
  | tooManyFragments (size : Nat)
deriving Repr, BEq, Inhabited

instance : ToString LenetError where
  toString
    | .noFreePeerSlots            => "no available peer slots for initiating connection"
    | .invalidPeerId p            => s!"invalid peerId {p}"
    | .peerNotConnected p         => s!"cannot send packet: peer {p} is not connected"
    | .invalidChannelId p c n     => s!"invalid channel ID {c} for peer {p} (peer has {n} channels)"
    | .tooManyFragments sz        => s!"packet of {sz} bytes exceeds maximum allowable fragment count"

end Lenet
