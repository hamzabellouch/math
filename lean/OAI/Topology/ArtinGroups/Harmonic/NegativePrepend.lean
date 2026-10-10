import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketOrbit
import OAI.Topology.ArtinGroups.Harmonic.CanonicalFusionLow
import OAI.Topology.ArtinGroups.Harmonic.FusionExpandedWordAction

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E V:Type} {K:Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E→ℕ) (d:V→V→FusionEdge E) (hd:∀ s t,d s t=d t s)
  (hdiag:∀ s,d s s=.units 0)
local notation "Q" => fusionQuiver m d hd
local notation "hn" => fusionQuiver_no_loops m d hd hdiag
local notation "P" => fusionWordPacketPerm m d hd hdiag (K:=K)

def negativePrepend (w:List V) (z:List (V×Bool)) : List (V×Bool) :=
  ((w.map fun s=>(s,true)).reverse.map fun a=>(a.1,!a.2))++z

lemma fusionExpandedInverse_action (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q (fusionExpandedWord m w) x=(P (w.map fun s=>(s,true))).symm x := by
  apply (P (w.map fun s=>(s,true))).injective
  rw [Equiv.apply_symm_apply,← fusionExpandedWord_action,positive_inverseWord Q hn]

lemma fusionPacketOrbit_negativePrepend (w:List V) (z:List (V×Bool)) (s:V) (L:FusionLabel m) :
    fusionPacketOrbit m d hd hdiag (negativePrepend w z) s L=
      inverseWordAction Q (fusionExpandedWord m w) (fusionPacketOrbit m d hd hdiag z s L) := by
  simp only [fusionPacketOrbit,negativePrepend,fusionWordPacketPerm_append,fusionWordPacketPerm_inverse]
  rw [fusionExpandedInverse_action]
  rfl

end HarmonicArtin

end OAI
