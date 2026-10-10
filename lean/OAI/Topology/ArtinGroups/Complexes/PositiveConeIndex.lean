import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TestPlacement
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

def positiveConeIndex (f:Map Q E F) (α:V) :
    ((TestIndex Q E.placement α ⊕ I) ⊕ (TestIndex Q F.placement α ⊕ J)) ≃
      (TestIndex Q (f.cone Q).placement α ⊕ (I ⊕ J)) where
  toFun
    | .inl (.inl p) => .inl ⟨.inl p.1,p.2⟩
    | .inl (.inr i) => .inr (.inl i)
    | .inr (.inl p) => .inl ⟨.inr p.1,p.2⟩
    | .inr (.inr j) => .inr (.inr j)
  invFun
    | .inl ⟨.inl i,p⟩ => .inl (.inl ⟨i,p⟩)
    | .inl ⟨.inr j,p⟩ => .inr (.inl ⟨j,p⟩)
    | .inr (.inl i) => .inl (.inr i)
    | .inr (.inr j) => .inr (.inr j)
  left_inv := by intro k;rcases k with (p|i)|(p|j) <;> rfl
  right_inv := by intro k;rcases k with ⟨i|j,p⟩|(i|j) <;> rfl

def positiveConeSign (α:V) :
    ((TestIndex Q E.placement α ⊕ I) ⊕ (TestIndex Q F.placement α ⊕ J)) → Bool
  | .inl (.inl _) => true
  | _ => false

omit [DecidableEq I] [DecidableEq J] in
lemma positiveCone_placement (f:Map Q E F) (α:V) :
    ((f.positiveTwist Q α).cone Q).placement =
      (((f.cone Q).positiveTwist Q α).reindex Q (positiveConeIndex Q f α)).placement := by
  funext k
  rcases k with (p|i)|(p|j) <;> rfl

lemma positiveCone_differential (f:Map Q E F) (α:V)
    (i j:(TestIndex Q E.placement α ⊕ I) ⊕ (TestIndex Q F.placement α ⊕ J)) :
    (if positiveConeSign Q (E:=E) (F:=F) α j then
      -((((f.cone Q).positiveTwist Q α).reindex Q (positiveConeIndex Q f α)).differential i j)
     else (((f.cone Q).positiveTwist Q α).reindex Q (positiveConeIndex Q f α)).differential i j) =
    (if positiveConeSign Q (E:=E) (F:=F) α i then
      -(((f.positiveTwist Q α).cone Q).differential i j)
     else ((f.positiveTwist Q α).cone Q).differential i j) := by
  rcases i with (p|i)|(p|i) <;> rcases j with (r|j)|(r|j)
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * (-E.differential p.1 r.1)) r.2.val) • vertexId Q α)) =
      -(-(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * E.differential p.1 r.1) r.2.val) • vertexId Q α)))
    simp only [neg_neg,mul_neg,map_neg,Pi.neg_apply,neg_smul]
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inl p.1,p.2⟩ (.inl j) =
      -(-evaluationMatrix Q E.placement α p j)
    simp only [evaluationMatrix,Sum.inl.injEq,neg_neg]
    split_ifs <;> rfl
  · rfl
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inl p.1,p.2⟩ (.inr j) = -(0:Q.Zigzag K)
    simp only [evaluationMatrix,Sum.inl_ne_inr,ite_false,neg_zero]
  · change -(0:Q.Zigzag K)= -0
    simp only [neg_zero]
  · rfl
  · rfl
  · rfl
  · change -(-((pathCoordinates Q (pathBasis Q (K:=K) p.2.val * 0) r.2.val) • vertexId Q α))=0
    simp only [mul_zero,map_zero,Pi.zero_apply,zero_smul,neg_zero]
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inr p.1,p.2⟩ (.inl j)=0
    simp only [evaluationMatrix,Sum.inr_ne_inl,ite_false]
  · rfl
  · change evaluationMatrix Q (f.cone Q).placement α ⟨.inr p.1,p.2⟩ (.inr j)=
      evaluationMatrix Q F.placement α p j
    simp only [evaluationMatrix,Sum.inr.injEq]
    split_ifs <;> rfl
  · change -(0:Q.Zigzag K)=0
    simp only [neg_zero]
  · rfl
  · rfl
  · rfl

noncomputable def positiveTwistCone (f:Map Q E F) (α:V) :
    ChainIsomorphism Q ((f.cone Q).positiveTwist Q α) ((f.positiveTwist Q α).cone Q) :=
  (reindexChainIsomorphism Q _ (positiveConeIndex Q f α)).trans Q
    (signChainIsomorphism Q _ _ (positiveConeSign Q α)
      (positiveCone_placement Q f α) (positiveCone_differential Q f α))

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
