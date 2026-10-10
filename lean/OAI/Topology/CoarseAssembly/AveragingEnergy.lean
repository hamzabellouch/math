import OAI.Topology.CoarseAssembly.SpatialAveraging

namespace OAI

/-! # Energy estimate for the actual lazy averages -/

noncomputable section

namespace CoarseAssembly

open Congruence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def translationEnergy (S : Finset ArithmeticGroup) (k : ℕ)
    (x : lp (fun _ : Quotient k => H) 2) : ℝ :=
  ∑ s ∈ S, ‖leftTranslation (Quotient k) (reduce k s) x - x‖ ^ 2

omit [CompleteSpace H] in
theorem translationEnergy_nonneg (S : Finset ArithmeticGroup) (k : ℕ)
    (x : lp (fun _ : Quotient k => H) 2) : 0 ≤ translationEnergy S k x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [CompleteSpace H] in
theorem translation_real_inner (k : ℕ) (s : ArithmeticGroup)
    (x : lp (fun _ : Quotient k => H) 2) :
    (inner ℂ x (leftTranslation (Quotient k) (reduce k s) x)).re =
      ‖x‖ ^ 2 - ‖leftTranslation (Quotient k) (reduce k s) x - x‖ ^ 2 / 2 := by
  have h := norm_sub_sq (𝕜 := ℂ) (leftTranslation (Quotient k) (reduce k s) x) x
  rw [(leftTranslation (Quotient k) (reduce k s)).norm_map, inner_re_symm] at h
  change ‖leftTranslation (Quotient k) (reduce k s) x - x‖ ^ 2 =
    ‖x‖ ^ 2 - 2 * (inner ℂ x (leftTranslation (Quotient k) (reduce k s) x)).re + ‖x‖ ^ 2 at h
  linarith

omit [CompleteSpace H] in
theorem meanTranslation_real_inner (S : Finset ArithmeticGroup) (hS : S.Nonempty)
    (k : ℕ) (x : lp (fun _ : Quotient k => H) 2) :
    (inner ℂ x (meanTranslation S k x)).re =
      ‖x‖ ^ 2 - translationEnergy S k x / (2 * S.card) := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hm : meanTranslation S k x = (S.card : ℂ)⁻¹ •
      ∑ s ∈ S, leftTranslation (Quotient k) (reduce k s) x := by
    simp only [meanTranslation, smul_apply, sum_apply]
    rfl
  rw [hm, inner_smul_right]
  have hc : (S.card : ℂ)⁻¹ = ((S.card : ℝ)⁻¹ : ℂ) := by simp
  rw [hc]
  simp only [← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    inner_sum, Complex.re_sum, translation_real_inner, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div]
  unfold translationEnergy
  field_simp

/-- Laziness turns the displacement-energy bound into a norm-square loss. -/
theorem lazyAverage_norm_sq_le (S : Finset ArithmeticGroup) (hS : S.Nonempty)
    (k : ℕ) (x : lp (fun _ : Quotient k => H) 2) :
    ‖lazyAverage S k x‖ ^ 2 ≤
      ‖x‖ ^ 2 - translationEnergy S k x / (4 * S.card) := by
  have hm : ‖meanTranslation S k x‖ ≤ ‖x‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (meanTranslation_norm_le S k))
  have he := meanTranslation_real_inner S hS k x
  have ha : lazyAverage S k x = (1 / 2 : ℂ) • (x + meanTranslation S k x) := rfl
  rw [ha, norm_smul, mul_pow, norm_add_sq (𝕜 := ℂ)]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have hdiv : translationEnergy S k x / (4 * S.card) =
      (translationEnergy S k x / (2 * S.card)) / 2 := by ring
  rw [hdiv]
  change ‖meanTranslation S k x‖ ≤ ‖x‖ at hm
  change RCLike.re (inner ℂ x (meanTranslation S k x)) =
    ‖x‖ ^ 2 - translationEnergy S k x / (2 * S.card) at he
  nlinarith [norm_nonneg (meanTranslation S k x), norm_nonneg x]

variable (Q : Type*) [Fintype Q] [Nonempty Q]

theorem constantProjection_complement_zero (x : lp (fun _ : Q => H) 2) :
    constantProjection Q (x - constantProjection Q x) = 0 := by
  rw [map_sub]
  have h := DFunLike.congr_fun (constantProjection_idempotent (H := H) Q) x
  change constantProjection Q (constantProjection Q x) = constantProjection Q x at h
  rw [h, sub_self]

theorem constantProjection_complement_norm_le (x : lp (fun _ : Q => H) 2) :
    ‖x - constantProjection Q x‖ ≤ ‖x‖ := by
  let U := (fiberConstantIsometry (H := H) Q).toContinuousLinearMap
  have hi : inner ℂ x (constantProjection Q x) = inner ℂ (U.adjoint x) (U.adjoint x) := by
    exact (ContinuousLinearMap.adjoint_inner_left U (U.adjoint x) x).symm
  have hn : ‖constantProjection Q x‖ = ‖U.adjoint x‖ :=
    (fiberConstantIsometry (H := H) Q).norm_map (U.adjoint x)
  have hs := norm_sub_sq (𝕜 := ℂ) x (constantProjection Q x)
  change ‖x - constantProjection Q x‖ ^ 2 =
    ‖x‖ ^ 2 - 2 * (inner ℂ x (constantProjection Q x)).re + ‖constantProjection Q x‖ ^ 2 at hs
  have hr : (inner ℂ (U.adjoint x) (U.adjoint x)).re = ‖U.adjoint x‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (U.adjoint x)).symm
  rw [hi, hn, hr] at hs
  nlinarith [norm_nonneg (x - constantProjection Q x), norm_nonneg x,
    sq_nonneg ‖U.adjoint x‖]

/-- A uniform energy estimate off the constants implies the precise norm
contraction used by the spatial transfer. -/
theorem uniformAveragingGap_of_energy (S : Finset ArithmeticGroup) (hS : S.Nonempty)
    (ε : ℝ) (hε : 0 < ε) (hεcard : ε ≤ 4 * S.card)
    (henergy : ∀ (k : ℕ) (x : lp (fun _ : Quotient k => H) 2),
      constantProjection (Quotient k) x = 0 →
        ε * ‖x‖ ^ 2 ≤ translationEnergy S k x) : UniformAveragingGap S H := by
  have hd : 0 < (4 : ℝ) * S.card := mul_pos (by norm_num) (by exact_mod_cast hS.card_pos)
  have hdv : 0 < ε / (4 * S.card) := div_pos hε hd
  have hn : 0 ≤ 1 - ε / (4 * S.card) := sub_nonneg.mpr ((div_le_one hd).2 hεcard)
  let c := Real.sqrt (1 - ε / (4 * S.card))
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hcs : c ^ 2 = 1 - ε / (4 * S.card) := Real.sq_sqrt hn
  have hclt : c < 1 := by nlinarith
  have hb (k : ℕ) (x : lp (fun _ : Quotient k => H) 2)
      (hx : constantProjection (Quotient k) x = 0) : ‖lazyAverage S k x‖ ≤ c * ‖x‖ := by
    have hl := lazyAverage_norm_sq_le S hS k x
    have he := div_le_div_of_nonneg_right (henergy k x hx) hd.le
    have heq : ε * ‖x‖ ^ 2 / (4 * S.card) = (ε / (4 * S.card)) * ‖x‖ ^ 2 := by ring
    rw [heq] at he
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).1
    rw [mul_pow, hcs]
    nlinarith
  refine ⟨c, hc, hclt, ?_⟩
  intro k
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  let y := x - constantProjection (Quotient k) x
  have hy : constantProjection (Quotient k) y = 0 := constantProjection_complement_zero _ x
  have hm := DFunLike.congr_fun (lazyAverage_projection (H := H) S hS k) x
  change lazyAverage S k (constantProjection (Quotient k) x) = constantProjection (Quotient k) x at hm
  have heq : (lazyAverage (H := H) S k - constantProjection (H := H) (Quotient k)) x = lazyAverage S k y := by
    change lazyAverage S k x - constantProjection (Quotient k) x =
      lazyAverage S k (x - constantProjection (Quotient k) x)
    rw [map_sub, hm]
  rw [heq]
  exact (hb k y hy).trans (mul_le_mul_of_nonneg_left (constantProjection_complement_norm_le _ x) hc)

end CoarseAssembly

end

end OAI
