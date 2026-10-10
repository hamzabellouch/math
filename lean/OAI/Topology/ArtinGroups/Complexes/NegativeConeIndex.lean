import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CotestPlacement
import OAI.Topology.ArtinGroups.Complexes.CoconePlacement
import OAI.Topology.ArtinGroups.Complexes.Refl
import OAI.Topology.ArtinGroups.Quivers.SignDiagonal

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
open Matrix

attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}

def negativeConeIndex (f:Map Q E F) (α:V) :
    ((I ⊕ TestIndex Q E.placement α) ⊕ (J ⊕ TestIndex Q F.placement α)) ≃
      ((I ⊕ J) ⊕ TestIndex Q (f.cone Q).placement α) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr p) => .inr ⟨.inl p.1,p.2⟩
    | .inr (.inl j) => .inl (.inr j)
    | .inr (.inr p) => .inr ⟨.inr p.1,p.2⟩
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr j) => .inr (.inl j)
    | .inr ⟨.inl i,p⟩ => .inl (.inr ⟨i,p⟩)
    | .inr ⟨.inr j,p⟩ => .inr (.inr ⟨j,p⟩)
  left_inv := by
    intro k; rcases k with (i|p)|(j|p) <;> rfl
  right_inv := by
    intro k; rcases k with (i|j)|⟨i|j,p⟩ <;> rfl

def negativeConeSign (α:V) :
    ((I ⊕ TestIndex Q E.placement α) ⊕ (J ⊕ TestIndex Q F.placement α)) → Bool
  | .inl (.inr _) => true
  | _ => false

omit [DecidableEq I] [DecidableEq J] in
lemma negativeCone_placement (f:Map Q E F) (α:V) :
    ((f.negativeTwist Q α).cone Q).placement =
      (((f.cone Q).negativeTwist Q α).reindex Q (negativeConeIndex Q f α)).placement := by
  funext k
  rcases k with (i|p)|(j|p)
  · rfl
  · change GeneratorPlacement.mk α ((E.placement p.1).cochain+1-1)
        ((E.placement p.1).internal+Path.length p.2.val-2) =
      GeneratorPlacement.mk α ((E.placement p.1).cochain-1+1)
        ((E.placement p.1).internal+Path.length p.2.val-2)
    congr 1
    omega
  · rfl
  · rfl

lemma negativeCone_differential (f:Map Q E F) (α:V)
    (i j:(I ⊕ TestIndex Q E.placement α) ⊕ (J ⊕ TestIndex Q F.placement α)) :
    (if negativeConeSign Q (E:=E) (F:=F) α j then
      -((((f.cone Q).negativeTwist Q α).reindex Q (negativeConeIndex Q f α)).differential i j)
     else (((f.cone Q).negativeTwist Q α).reindex Q (negativeConeIndex Q f α)).differential i j) =
    (if negativeConeSign Q (E:=E) (F:=F) α i then
      -(((f.negativeTwist Q α).cone Q).differential i j)
     else ((f.negativeTwist Q α).cone Q).differential i j) := by
  rcases i with (i|p)|(i|p) <;> rcases j with (j|r)|(j|r)
  · rfl
  · change -coevaluationMatrix Q (f.cone Q).placement α (.inl i) ⟨.inl r.1,r.2⟩ =
      -coevaluationMatrix Q E.placement α i r
    simp only [coevaluationMatrix, Sum.inl.injEq]
    split_ifs <;> rfl
  · rfl
  · change coevaluationMatrix Q (f.cone Q).placement α (.inl i) ⟨.inr r.1,r.2⟩ = 0
    simp only [coevaluationMatrix, Sum.inl_ne_inr,ite_false]
  · change (0:Q.Zigzag K)= -(-0)
    simp only [neg_zero]
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * (-E.differential p.1 r.1)) r.2.val) • vertexId Q α)) =
      -(-(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * E.differential p.1 r.1) r.2.val) • vertexId Q α)))
    simp only [neg_neg,mul_neg,map_neg,Pi.neg_apply,neg_smul]
  · change (0:Q.Zigzag K)= -0
    simp only [neg_zero]
  · rfl
  · rfl
  · change -coevaluationMatrix Q (f.cone Q).placement α (.inr i) ⟨.inl r.1,r.2⟩ = 0
    simp only [coevaluationMatrix, Sum.inr_ne_inl,ite_false,neg_zero]
  · rfl
  · change coevaluationMatrix Q (f.cone Q).placement α (.inr i) ⟨.inr r.1,r.2⟩ =
      coevaluationMatrix Q F.placement α i r
    simp only [coevaluationMatrix, Sum.inr.injEq]
    split_ifs <;> rfl
  · rfl
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * 0) r.2.val) • vertexId Q α))=0
    simp only [mul_zero,map_zero,Pi.zero_apply,zero_smul,neg_zero]
  · rfl
  · rfl

noncomputable def negativeTwistCone (f:Map Q E F) (α:V) :
    ChainIsomorphism Q ((f.cone Q).negativeTwist Q α) ((f.negativeTwist Q α).cone Q) :=
  (reindexChainIsomorphism Q _ (negativeConeIndex Q f α)).trans Q
    (signChainIsomorphism Q _ _ (negativeConeSign Q α)
      (negativeCone_placement Q f α) (negativeCone_differential Q f α))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
