import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketPerm
import OAI.Topology.ArtinGroups.Complexes.PositiveWordActionAppend
import OAI.Topology.ArtinGroups.Harmonic.RowReflect
import OAI.Topology.ArtinGroups.Complexes.PacketPermEnumeration

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

lemma fusionExpandedWord_action (w : List V) (x : FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q (fusionExpandedWord m w) x=
      fusionWordPacketPerm m d hd hdiag (w.map fun s => (s,true)) x := by
  induction w generalizing x with
  | nil => rfl
  | cons s w ih =>
    change positiveWordAction Q (((Finset.univ : Finset (FusionLabel m)).toList.map (fun L => (s,L)))++
      fusionExpandedWord m w) x=_
    rw [positiveWordAction_append,ih,positiveWordAction_eq_prod Q hn,List.map_map,Function.comp_def,
      classPacketPerm_toList Q hn (fun L => (s,L)) (fusionColor_orthogonal m d hd hdiag s)]
    rfl

end HarmonicArtin

end OAI
