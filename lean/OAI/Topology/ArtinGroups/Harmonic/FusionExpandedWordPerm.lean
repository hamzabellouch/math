import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionExpandedWordAction

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V : Type} {K : Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t,d s t=d t s)
  (hdiag : ∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag

lemma fusionExpandedWord_perm (w : List V) :
    ((fusionExpandedWord m w).map (classTwistPerm Q (K:=K) hn)).prod=
      fusionWordPacketPerm m d hd hdiag (w.map fun s => (s,true)) := by
  apply Equiv.ext
  intro x
  rw [← positiveWordAction_eq_prod Q hn,fusionExpandedWord_action]

end HarmonicArtin

end OAI
