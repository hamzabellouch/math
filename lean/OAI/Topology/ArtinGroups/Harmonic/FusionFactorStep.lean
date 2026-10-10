import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Iso
import OAI.Topology.ArtinGroups.Harmonic.FusionRest

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq
variable {E V : Type} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m:E → ℕ) (e:E) (d:V → V → FusionEdge E) (hd:∀ s t,d s t=d t s)

omit [Fintype E] in
@[simp] lemma labelSplit_symm_rest (r:FusionLabel (fun f:FusionRest e => m f)) (a:StringLabel (m e)) :
    restLabel m e ((labelSplit m e).symm (r,a)) = r :=
  congrArg Prod.fst ((labelSplit m e).apply_symm_apply (r,a))

omit [Fintype E] in
@[simp] lemma labelSplit_symm_at (r:FusionLabel (fun f:FusionRest e => m f)) (a:StringLabel (m e)) :
    ((labelSplit m e).symm (r,a)) e = a :=
  congrArg Prod.snd ((labelSplit m e).apply_symm_apply (r,a))

omit [Fintype V] [DecidableEq V] in
@[ext] lemma fusionArrow_ext {a b:FusionQuiverArrow m d}
    (hl:a.1.1=b.1.1) (hr:a.1.2=b.1.2) (hk:a.2.val=b.2.val) : a=b := by
  rcases a with ⟨⟨α,β⟩,k⟩; rcases b with ⟨⟨α',β'⟩,k'⟩
  dsimp at hl hr hk
  subst α'; subst β'
  exact congrArg (Sigma.mk (α,β)) (Fin.ext hk)

include hd in
omit [Fintype E] [Fintype V] [DecidableEq V] in
private lemma restEdge_symm : ∀ s t,(d s t).removeFactor e=(d t s).removeFactor e :=
  fun s t => congrArg (FusionEdge.removeFactor e) (hd s t)

local notation "mr" => (fun f:FusionRest e => m f)
local notation "dr" => (fun s t => FusionEdge.removeFactor e (d s t))
local notation "Qr" => fusionQuiver mr dr (restEdge_symm e d hd)
local notation "Q" => fusionQuiver m d hd

noncomputable def fusionFactorStep (a:FusionQuiverArrow mr dr) : Bool :=
  (d a.1.1.1 a.1.2.1).usesFactor e

omit [Fintype V] [DecidableEq V] in
lemma fusionFactorStep_reverse (a:FusionQuiverArrow mr dr) :
    fusionFactorStep m e d ((Qr).reverse a) = fusionFactorStep m e d a := by
  change (d a.1.2.1 a.1.1.1).usesFactor e = (d a.1.1.1 a.1.2.1).usesFactor e
  rw [hd]

local notation "step" => fusionFactorStep m e d
local notation "N" => stringAdjacent (m e)
local notation "U" => ReversibleQuiver.stringQuiver Qr step (fusionFactorStep_reverse m e d hd) N (stringAdjacent_symm (m e))

noncomputable def fusionArrowSplit (a:FusionQuiverArrow m d) : StringArrow step N := by
  have hM := (d a.1.1.1 a.1.2.1).multiplicity_split m e a.1.1.2 a.1.2.2
  have hP : if (d a.1.1.1 a.1.2.1).usesFactor e then N (a.1.1.2 e) (a.1.2.2 e)
      else a.1.1.2 e=a.1.2.2 e := by
    by_contra h
    have hk : 0 < (d a.1.1.1 a.1.2.1).multiplicity m a.1.1.2 a.1.2.2 := Nat.zero_lt_of_lt a.2.isLt
    rw [hM,ite_eq_right h] at hk
    exact Nat.lt_irrefl 0 hk
  have hk : a.2.val < ((d a.1.1.1 a.1.2.1).removeFactor e).multiplicity mr
      (restLabel m e a.1.1.2) (restLabel m e a.1.2.2) := by
    exact lt_of_lt_of_le a.2.isLt (le_of_eq (hM.trans (ite_eq_left hP)))
  exact ⟨(⟨((a.1.1.1,restLabel m e a.1.1.2),(a.1.2.1,restLabel m e a.1.2.2)),⟨a.2.val,hk⟩⟩,
    a.1.1.2 e,a.1.2.2 e),hP⟩

noncomputable def fusionArrowJoin (a:StringArrow step N) : FusionQuiverArrow m d := by
  let α := (fusionVertexSplit (V:=V) m e).symm ((Qr).source a.base,a.left)
  let β := (fusionVertexSplit (V:=V) m e).symm ((Qr).target a.base,a.right)
  refine ⟨(α,β),⟨a.base.2.val,?_⟩⟩
  have hM := (d α.1 β.1).multiplicity_split m e α.2 β.2
  dsimp [α,β,fusionVertexSplit] at hM ⊢
  simp only [labelSplit_symm_at,labelSplit_symm_rest] at hM
  rw [hM]
  change a.base.2.val < (if (if step a.base then N a.left a.right else a.left=a.right) then
    ((d a.base.1.1.1 a.base.1.2.1).removeFactor e).multiplicity mr a.base.1.1.2 a.base.1.2.2 else 0)
  have hp : if step a.base then N a.left a.right else a.left=a.right := a.property
  exact lt_of_lt_of_le a.base.2.isLt (le_of_eq (ite_eq_left hp).symm)

omit [Fintype V] [DecidableEq V] in
lemma fusionArrowJoin_split (a:FusionQuiverArrow m d) :
    fusionArrowJoin m e d hd (fusionArrowSplit m e d a) = a := by
  apply fusionArrow_ext
  · exact Prod.ext rfl ((labelSplit m e).symm_apply_apply a.1.1.2)
  · exact Prod.ext rfl ((labelSplit m e).symm_apply_apply a.1.2.2)
  · rfl

omit [Fintype V] [DecidableEq V] in
lemma fusionArrowSplit_join (a:StringArrow step N) :
    fusionArrowSplit m e d (fusionArrowJoin m e d hd a) = a := by
  apply StringArrow.ext
  · apply fusionArrow_ext
    · exact Prod.ext rfl (labelSplit_symm_rest m e _ _)
    · exact Prod.ext rfl (labelSplit_symm_rest m e _ _)
    · rfl
  · exact labelSplit_symm_at m e _ _
  · exact labelSplit_symm_at m e _ _

noncomputable def fusionQuiverSplit : Iso Q U where
  vertex := fusionVertexSplit m e
  arrow :=
    { toFun := fusionArrowSplit m e d
      invFun := fusionArrowJoin m e d hd
      left_inv := fusionArrowJoin_split m e d hd
      right_inv := fusionArrowSplit_join m e d hd }
  source _ := rfl
  target _ := rfl
  reverse a := by
    apply StringArrow.ext
    · apply fusionArrow_ext <;> rfl
    · rfl
    · rfl

end HarmonicArtin

end OAI
