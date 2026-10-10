import Mathlib
import OAI.Topology.ArtinGroups.Quivers.SimpleEdge

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge

variable {V A : Type*} (Q : ReversibleQuiver V A) {α β : V}

lemma ext_arrow {e f : SimpleEdge Q α β} (h : e.arrow = f.arrow) : e = f := by
  cases e
  cases f
  cases h
  rfl

@[simp] lemma reverse_reverse (e : SimpleEdge Q α β) : (e.reverse Q).reverse Q = e := by
  apply ext_arrow Q
  exact Q.reverse_reverse e.arrow

end HarmonicArtin.ReversibleQuiver.Zigzag.SimpleEdge

end OAI
