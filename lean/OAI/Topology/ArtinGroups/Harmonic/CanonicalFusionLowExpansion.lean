import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionLow
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

lemma canonicalFusionLow_eq_expansion (w : List V) (q : ℤ)
    (x : FiniteHomotopyClass Q (K:=K)) :
    canonicalFusionLow m d hd hdiag w q x=canonicalWordLow Q (fusionExpandedWord m w) q x := by
  apply canonicalFusionLow_eq_ordinary m d hd hdiag w (fusionExpandedWord m w)
  intro y
  exact fusionExpandedWord_action m d hd hdiag w y

end HarmonicArtin

end OAI
