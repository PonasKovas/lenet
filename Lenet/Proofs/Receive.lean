import Lenet.Peer

/-!
# What `Peer.receiveOnChannel` computes

It takes the channel out of the peer (`takeAt`) so the receive step holds it
once; as a value that is the old shape, the channel replaced in place.
Proofs about the receive path rewrite with these instead of unfolding it.
-/

namespace Lenet.Proofs

open Peer

theorem receiveOnChannel_eq (p : Peer) (c : UInt8) (r : Channel → Channel × Array Packet)
    (h : c.toNat < p.channels.size) :
    p.receiveOnChannel c r =
      (({ p with channels := p.channels.set c.toNat (r p.channels[c.toNat]).1 h } : Peer).pruneAssemblers c,
        (r p.channels[c.toNat]).2.map (Event.receive p.peerId c)) := by
  unfold receiveOnChannel
  rw [dif_pos h]
  dsimp only
  rw [takeAt_eq]
  dsimp only
  rw [set_setIfInBounds_same]

theorem receiveOnChannel_out (p : Peer) (c : UInt8) (r : Channel → Channel × Array Packet)
    (h : ¬ c.toNat < p.channels.size) : p.receiveOnChannel c r = (p, #[]) := by
  unfold receiveOnChannel
  rw [dif_neg h]

end Lenet.Proofs
