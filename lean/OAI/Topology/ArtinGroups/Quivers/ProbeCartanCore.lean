import Mathlib
import OAI.Topology.ArtinGroups.Complexes.GeneratorVector
import OAI.Topology.ArtinGroups.Quivers.ProbeVertex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
open Zigzag Zigzag.BasedComplex Matrix

variable {V A:Type*} (Q:ReversibleQuiver V A) [Fintype V]
attribute [local instance] Classical.decEq Classical.propDecidable
local notation "R" => probeQuiver Q

omit [Fintype V] in
lemma probeCartan_core (α β:V) : unfoldedCartan R (.inl α) (.inl β)=unfoldedCartan Q α β := by
  unfold unfoldedCartan
  simp only [Sum.inl.injEq]
  congr 2
  apply Nat.card_congr
  refine {
    toFun:=?_
    invFun:=fun a=>⟨.inl a.val,congrArg Sum.inl a.property.1,congrArg Sum.inl a.property.2⟩
    left_inv:=?_
    right_inv:=?_ }
  · rintro ⟨a,ha⟩
    cases a with
    | inl a=>exact ⟨a,Sum.inl.inj ha.1,Sum.inl.inj ha.2⟩
    | inr p=>
      rcases p with ⟨v,b,c⟩
      cases c
      · exact False.elim (Sum.inr_ne_inl ha.2)
      · exact False.elim (Sum.inr_ne_inl ha.1)
  · rintro ⟨a,ha⟩
    cases a with
    | inl a=>rfl
    | inr p=>
      rcases p with ⟨v,b,c⟩
      cases c
      · exact False.elim (Sum.inr_ne_inl ha.2)
      · exact False.elim (Sum.inr_ne_inl ha.1)
  · intro a; rfl

omit [Fintype V] in
lemma probeCartan_leaf_core (α β:V) (b:Bool) :
    unfoldedCartan R (.inr (α,b)) (.inl β)=if α=β then -1 else 0 := by
  unfold unfoldedCartan
  simp only [Sum.inr_ne_inl,ite_false,zero_sub]
  have he : {a:ProbeArrow V A // (probeQuiver Q).source a=.inr (α,b) ∧ (probeQuiver Q).target a=.inl β} ≃
      {u:Unit // α=β} := {
    toFun:=fun a=>⟨(),by
      have hs:=(probe_source_iff Q α b a.val).mp a.property.1
      have ht:=a.property.2
      rw [hs] at ht
      exact Sum.inl.inj ht⟩
    invFun:=fun a=>⟨.inr (α,b,true),rfl,congrArg Sum.inl a.property⟩
    left_inv:=by intro a; apply Subtype.ext; exact ((probe_source_iff Q α b a.val).mp a.property.1).symm
    right_inv:=by intro a; apply Subtype.ext; exact Subsingleton.elim _ _ }
  rw [Nat.card_congr he]
  by_cases h:α=β
  · simp [h]
  · simp [h]

lemma probeCartan_mul_core (p:V→ℝ) (α:V) :
    (unfoldedCartan R *ᵥ Sum.elim p (fun _=>0)) (.inl α)=(unfoldedCartan Q *ᵥ p) α := by
  simp only [mulVec,dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    MulZeroClass.mul_zero,Finset.sum_const_zero,add_zero,probeCartan_core]

lemma probeCartan_mul_leaf (p:V→ℝ) (α:V) (b:Bool) :
    (unfoldedCartan R *ᵥ Sum.elim p (fun _=>0)) (.inr (α,b))= -p α := by
  simp only [mulVec,dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    MulZeroClass.mul_zero,Finset.sum_const_zero,add_zero,probeCartan_leaf_core]
  simp

lemma probeCartan_pairing (n:ProbeVertex V→ℝ) (p:V→ℝ) :
    n ⬝ᵥ (unfoldedCartan R *ᵥ Sum.elim p (fun _=>0))=
      (fun α=>n (.inl α)) ⬝ᵥ (unfoldedCartan Q *ᵥ p)-
        ∑ α,∑ b:Bool,n (.inr (α,b))*p α := by
  simp only [dotProduct,Fintype.sum_sum_type,probeCartan_mul_core]
  conv_lhs => rhs; arg 2; ext a; rw [probeCartan_mul_leaf]
  simp only [mul_neg,Finset.sum_neg_distrib,Fintype.sum_prod_type,sub_eq_add_neg]

end HarmonicArtin.ReversibleQuiver

end OAI
