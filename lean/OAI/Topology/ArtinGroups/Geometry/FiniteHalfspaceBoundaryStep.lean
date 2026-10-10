import Mathlib

namespace OAI

namespace HarmonicArtin.Geometric
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]

theorem finite_halfspace_boundary_step (f : I → E →ₗ[ℝ] ℝ) (b : I → ℝ)
    (K : Set E) (hK : K = {x | ∀ i, f i x ≤ b i}) (hcpt : IsCompact K)
    (c x : E) (hc : c ∈ K) (hx : x ∈ K) (hne : x ≠ c) :
    ∃ (y : E) (t : ℝ) (i : I), y ∈ K ∧ 1 ≤ t ∧
      y = c + t • (x-c) ∧ f i y = b i ∧ f i c < b i := by
  have hc' : ∀ i, f i c ≤ b i := by simpa only [hK,Set.mem_ofPred_eq] using hc
  have hx' : ∀ i, f i x ≤ b i := by simpa only [hK,Set.mem_ofPred_eq] using hx
  let v := x-c
  have hv : v ≠ 0 := sub_ne_zero.mpr hne
  have hp : ∃ i, 0 < f i v := by
    by_contra hn
    push Not at hn
    obtain ⟨R,hR,hbound⟩ := hcpt.isBounded.exists_pos_norm_le
    let r : ℝ := (R+‖c‖+1)/‖v‖
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hrn : r * ‖v‖ = R+‖c‖+1 := div_mul_cancel₀ _ hnv.ne'
    have hm : c+r • v ∈ K := by
      rw [hK]
      intro i
      simp only [map_add,map_smul,smul_eq_mul]
      exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hr (hn i))).trans (hc' i)
    have hnorm := norm_sub_le (c+r • v) c
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,hrn] at hnorm
    have hh := hbound (c+r • v) hm
    linarith
  let J := Finset.univ.filter (fun i => 0 < f i v)
  have hJ : J.Nonempty := by obtain ⟨i,hi⟩ := hp; exact ⟨i,by simp [J,hi]⟩
  obtain ⟨i,hi,hmin⟩ := J.exists_min_image (fun j => (b j-f j c)/f j v) hJ
  have hi' : 0 < f i v := (Finset.mem_filter.mp hi).2
  let t := (b i-f i c)/f i v
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ hi').mpr
    dsimp [v]
    rw [map_sub]
    linarith [hx' i]
  have heq : t * f i v = b i-f i c := div_mul_cancel₀ _ hi'.ne'
  refine ⟨c+t • v,t,i,?_,ht,rfl,?_,?_⟩
  · rw [hK]
    intro j
    simp only [map_add,map_smul,smul_eq_mul]
    by_cases hj : 0 < f j v
    · have hh : t ≤ (b j-f j c)/f j v := hmin j (by simp [J,hj])
      have hh' := (le_div_iff₀ hj).mp hh
      linarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos (le_trans (by norm_num) ht) (le_of_not_gt hj)
      linarith [hc' j]
  · simp only [map_add,map_smul,smul_eq_mul]
    linarith
  · have hh : f i v = f i x-f i c := map_sub _ _ _
    linarith [hx' i]

lemma boundary_step_combo {c x y : E} {t : ℝ} (ht : 1 ≤ t)
    (he : y = c + t • (x-c)) :
    x = (1-t⁻¹) • c + t⁻¹ • y := by
  have hn : t ≠ 0 := by linarith
  rw [he,smul_add,smul_smul,inv_mul_cancel₀ hn,one_smul,sub_smul,one_smul]
  abel

lemma boundary_step_level {c x y : E} {t b : ℝ} (he : y = c+t • (x-c))
    (f : E →ₗ[ℝ] ℝ) (hc : f c = b) (hx : f x = b) : f y = b := by
  rw [he,map_add,map_smul,map_sub,hc,hx,sub_self,smul_zero,add_zero]

end HarmonicArtin.Geometric

end OAI
