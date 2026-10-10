import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightAffineValue

namespace OAI

namespace HarmonicArtin
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {P E : Type*} [PartialOrder P] [Fintype P] [AddCommGroup E] [Module ℝ E]
variable (z : P → E) (f : P → E →ₗ[ℝ] ℝ) (b : P → ℝ)
  (hle : ∀ p q,f q (z p) ≤ b q) (heq : ∀ p q,f q (z p) = b q ↔ p ≤ q)
include hle heq

lemma affine_weight_max_eq (x : OrderWeights P) :
    f (weightMax x) (weightAffineValue z x) = b (weightMax x) := by
  apply (weightAffineValue_eq_iff z x _ _ (fun p => hle p _)).mpr
  intro p hp
  exact (heq p _).mpr (le_weightMax x p hp)

lemma affine_weight_max_unique (x y : OrderWeights P)
    (h : weightAffineValue z x = weightAffineValue z y) : weightMax x = weightMax y := by
  apply le_antisymm
  · have hh := affine_weight_max_eq z f b hle heq y
    rw [←h] at hh
    have H := (weightAffineValue_eq_iff z x _ _ (fun p => hle p _)).mp hh
    exact (heq _ _).mp (H _ (weightMax_mem x))
  · have hh := affine_weight_max_eq z f b hle heq x
    rw [h] at hh
    have H := (weightAffineValue_eq_iff z y _ _ (fun p => hle p _)).mp hh
    exact (heq _ _).mp (H _ (weightMax_mem y))

omit heq in
lemma affine_weight_split_bound (y : OrderWeights P) (c d : P) :
    f d (weightAffineValue z y) ≤ (1-y.weights c)*b d+y.weights c*f d (z c) := by
  by_cases hc : y.weights c = 1
  · rw [weight_eq_vertex_of_one y c hc,weightAffineValue_vertex]
    simp only [weightVertex,Finsupp.single_eq_same]
    linarith
  · have hc' : y.weights c < 1 := lt_of_le_of_ne (weight_le_one y c) hc
    have hh := weightAffineValue_le z (weightDelete c y hc') (f d) (b d) (fun p => hle p d)
    rw [weightAffineValue_delete z y c hc',map_add,map_smul,map_smul]
    simp only [smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr (weight_le_one y c))) le_rfl

lemma affine_weight_max_coefficient_le (x y : OrderWeights P)
    (h : weightAffineValue z x = weightAffineValue z y) :
    y.weights (weightMax x) ≤ x.weights (weightMax x) := by
  let c := weightMax x
  by_cases hc : x.weights c = 1
  · rw [hc]; exact weight_le_one y c
  have hc' : x.weights c < 1 := lt_of_le_of_ne (weight_le_one x c) hc
  let x' := weightDelete c x hc'
  let d := weightMax x'
  have hd : d ∈ x.weights.support.erase c := weightDelete_support c x hc' (weightMax_mem x')
  have hdc : d < c := lt_of_le_of_ne (le_weightMax x d (Finset.mem_erase.mp hd).2)
    (Finset.mem_erase.mp hd).1
  have hstrict : f d (z c) < b d := lt_of_le_of_ne (hle c d)
    (fun H => (not_le_of_gt hdc) ((heq c d).mp H))
  have hex : f d (weightAffineValue z x) = (1-x.weights c)*b d+x.weights c*f d (z c) := by
    rw [weightAffineValue_delete z x c hc',map_add,map_smul,map_smul]
    change (1-x.weights c)*f d (weightAffineValue z x') + x.weights c*f d (z c) = _
    rw [affine_weight_max_eq z f b hle heq x']
  have hey := affine_weight_split_bound z f b hle y c d
  rw [←h,hex] at hey
  nlinarith

theorem weightAffineValue_injective : Function.Injective (weightAffineValue z) := by
  have H : ∀ n : ℕ, ∀ x : OrderWeights P, x.weights.support.card = n →
      ∀ y : OrderWeights P, weightAffineValue z x = weightAffineValue z y → x = y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hn y hxy
      let c := weightMax x
      have hm : weightMax y = c := (affine_weight_max_unique z f b hle heq x y hxy).symm
      have hcoeff : x.weights c = y.weights c := le_antisymm
        (by simpa only [hm] using affine_weight_max_coefficient_le z f b hle heq y x hxy.symm)
        (affine_weight_max_coefficient_le z f b hle heq x y hxy)
      by_cases hc : x.weights c = 1
      · exact (weight_eq_vertex_of_one x c hc).trans (weight_eq_vertex_of_one y c (hcoeff ▸ hc)).symm
      have hx : x.weights c < 1 := lt_of_le_of_ne (weight_le_one x c) hc
      have hy : y.weights c < 1 := hcoeff ▸ hx
      have hnon : 1-x.weights c ≠ 0 := ne_of_gt (sub_pos.mpr hx)
      have hdel : weightAffineValue z (weightDelete c x hx) = weightAffineValue z (weightDelete c y hy) := by
        rw [weightAffineValue_delete z x c hx,weightAffineValue_delete z y c hy,←hcoeff] at hxy
        exact smul_right_injective _ hnon (add_right_cancel hxy)
      have hcard : (weightDelete c x hx).weights.support.card < n := by
        rw [←hn]
        exact lt_of_le_of_lt (Finset.card_le_card (weightDelete_support c x hx))
          (Finset.card_erase_lt_of_mem (weightMax_mem x))
      have hw := ih _ hcard (weightDelete c x hx) rfl (weightDelete c y hy) hdel
      apply OrderWeights.ext
      ext p
      by_cases hp : p = c
      · subst p; exact hcoeff
      · have hv := congrArg (fun w : OrderWeights P => w.weights p) hw
        rw [weightDelete_apply,weightDelete_apply,ite_eq_right hp,ite_eq_right hp,←hcoeff] at hv
        exact mul_left_cancel₀ (inv_ne_zero hnon) hv
  intro x y h
  exact H _ x rfl y h

end HarmonicArtin

end OAI
