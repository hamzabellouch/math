import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.AltList
import OAI.Topology.ArtinGroups.Harmonic.FusionPacketPerm

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable

lemma alternating_lift_prod {S G : Type*} [Group G] (f : S → G) (i j : S) (n : ℕ) :
    FreeGroup.lift f (alternating i j n)=((altList i j n).map f).prod := by
  induction n generalizing i j with
  | zero => simp [alternating,altList]
  | succ n ih => simp only [alternating,map_mul,FreeGroup.lift_apply_of,altList_succ,
      List.map_cons,List.prod_cons,ih]

variable {E V : Type} {K : Type*} [Field K]
  [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t,d s t=d t s)
  (hdiag : ∀ s,d s s=.units 0)

lemma fusionWordPacketPerm_positive (w : List V) :
    fusionWordPacketPerm m d hd hdiag (K:=K) (w.map fun s => (s,true))=
      (w.map (fusionPacketPerm m d hd hdiag)).prod := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons,List.prod_cons,fusionWordPacketPerm,
      fusionSignedPacketPerm,ite_true,ih]

end HarmonicArtin

end OAI
