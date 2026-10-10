import OAI.RepresentationTheory.VertexAlgebra.Foundations

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)

lemma jet_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv k φ) (iteratedDeriv (k+1) φ x) x := by
  rw [iteratedDeriv_succ]
  exact (φ.smooth.differentiable_iteratedDeriv k (by exact_mod_cast ENat.natCast_lt_top k) x).hasDerivAt

lemma velocity_second_formula (t x : ℝ) :
    iteratedDeriv 2 (φ.velocity t) x =
      deriv Real.smoothTransition t * iteratedDeriv 2 φ (φ.inverse t x) /
        φ.jacobian t (φ.inverse t x)^3 := by
  have hfun : deriv (φ.velocity t) = fun z =>
      deriv Real.smoothTransition t * (deriv φ (φ.inverse t z)-1) /
        φ.jacobian t (φ.inverse t z) :=
    funext fun z => (φ.velocity_space_derivative t z).deriv
  have hi := φ.inverse_space_derivative t x
  have h2 := (φ.jet_hasDerivAt 1 (φ.inverse t x)).comp x hi
  rw [iteratedDeriv_one] at h2
  have hj := (φ.jacobian_space_derivative t (φ.inverse t x)).comp x hi
  have hd := ((h2.sub_const 1).const_mul (deriv Real.smoothTransition t)).div hj
    (ne_of_gt (φ.jacobian_pos t (φ.inverse t x)))
  simp only [Function.comp_def] at hd
  rw [show (2:ℕ)=1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, hfun]
  calc _ = _ := hd.deriv
       _ = _ := by
         have hne := ne_of_gt (φ.jacobian_pos t (φ.inverse t x))
         simp only [iteratedDeriv_succ, iteratedDeriv_zero]
         field_simp [hne]
         simp only [jacobian]
         ring

lemma velocity_third_formula (t x : ℝ) :
    iteratedDeriv 3 (φ.velocity t) x = deriv Real.smoothTransition t *
      (iteratedDeriv 3 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^4 -
        3 * Real.smoothTransition t * (iteratedDeriv 2 φ (φ.inverse t x))^2 /
          φ.jacobian t (φ.inverse t x)^5) := by
  have hfun : iteratedDeriv 2 (φ.velocity t) = fun z =>
      deriv Real.smoothTransition t * iteratedDeriv 2 φ (φ.inverse t z) /
        φ.jacobian t (φ.inverse t z)^3 := funext (φ.velocity_second_formula t)
  have hi := φ.inverse_space_derivative t x
  have h3 := (φ.jet_hasDerivAt 2 (φ.inverse t x)).comp x hi
  have hj := (φ.jacobian_space_derivative t (φ.inverse t x)).comp x hi
  have hd := (h3.const_mul (deriv Real.smoothTransition t)).div (hj.pow 3)
    (pow_ne_zero _ (ne_of_gt (φ.jacobian_pos t (φ.inverse t x))))
  simp only [Function.comp_def, Pi.pow_apply] at hd
  rw [show (3:ℕ)=2+1 by rfl, iteratedDeriv_succ, hfun]
  calc _ = _ := hd.deriv
       _ = _ := by
         have hne := ne_of_gt (φ.jacobian_pos t (φ.inverse t x))
         simp only [iteratedDeriv_succ, iteratedDeriv_zero]
         field_simp [hne]
         ring

lemma velocity_fourth_formula (t x : ℝ) :
    iteratedDeriv 4 (φ.velocity t) x = deriv Real.smoothTransition t *
      (iteratedDeriv 4 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^5 -
        10 * Real.smoothTransition t * iteratedDeriv 2 φ (φ.inverse t x) *
          iteratedDeriv 3 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^6 +
        15 * Real.smoothTransition t^2 * (iteratedDeriv 2 φ (φ.inverse t x))^3 /
          φ.jacobian t (φ.inverse t x)^7) := by
  have hfun : iteratedDeriv 3 (φ.velocity t) = fun z => deriv Real.smoothTransition t *
      (iteratedDeriv 3 φ (φ.inverse t z) / φ.jacobian t (φ.inverse t z)^4 -
        3 * Real.smoothTransition t * (iteratedDeriv 2 φ (φ.inverse t z))^2 /
          φ.jacobian t (φ.inverse t z)^5) := funext (φ.velocity_third_formula t)
  have hi := φ.inverse_space_derivative t x
  have h3 := (φ.jet_hasDerivAt 2 (φ.inverse t x)).comp x hi
  have h4 := (φ.jet_hasDerivAt 3 (φ.inverse t x)).comp x hi
  have hj := (φ.jacobian_space_derivative t (φ.inverse t x)).comp x hi
  have hne := ne_of_gt (φ.jacobian_pos t (φ.inverse t x))
  have hd := ((h4.div (hj.pow 4) (pow_ne_zero _ hne)).sub
    (((h3.pow 2).const_mul (3*Real.smoothTransition t)).div (hj.pow 5)
      (pow_ne_zero _ hne))).const_mul (deriv Real.smoothTransition t)
  simp only [Function.comp_def, Pi.div_apply, Pi.pow_apply, Pi.sub_apply] at hd
  rw [show (4:ℕ)=3+1 by rfl, iteratedDeriv_succ, hfun]
  calc _ = _ := hd.deriv
       _ = _ := by
         simp only [iteratedDeriv_succ, iteratedDeriv_zero]
         field_simp [hne]
         ring

lemma jacobian_lower_near_identity {ε : ℝ} (hε : ε ≤ 1/2)
    (h1 : ∀ x, |deriv φ x-1| ≤ ε) (t y : ℝ) : 1/2 ≤ φ.jacobian t y := by
  have hd := (abs_le.mp (h1 y)).1
  have hb0 := Real.smoothTransition.nonneg t
  have hb1 := Real.smoothTransition.le_one t
  have he : -(Real.smoothTransition t)*ε ≤
      Real.smoothTransition t*(deriv φ y-1) := by nlinarith
  dsimp only [jacobian]
  nlinarith

lemma velocity_fourth_bound {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2)
    (h1 : ∀ x, |deriv φ x-1| ≤ ε)
    (hk : ∀ k ∈ Finset.Icc 2 4, ∀ x, |iteratedDeriv k φ x| ≤ ε)
    (t x : ℝ) :
    |iteratedDeriv 4 (φ.velocity t) x| ≤ 2592*|deriv Real.smoothTransition t| *ε := by
  have hJ := φ.jacobian_lower_near_identity hε1 h1 t (φ.inverse t x)
  have hJ0 := φ.jacobian_pos t (φ.inverse t x)
  have hb0 := Real.smoothTransition.nonneg t
  have hb1 := Real.smoothTransition.le_one t
  have h2 := hk 2 (by norm_num) (φ.inverse t x)
  have h3 := hk 3 (by norm_num) (φ.inverse t x)
  have h4 := hk 4 (by norm_num) (φ.inverse t x)
  rw [φ.velocity_fourth_formula, abs_mul]
  have hi : |iteratedDeriv 4 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^5 -
        10*Real.smoothTransition t*iteratedDeriv 2 φ (φ.inverse t x)*
          iteratedDeriv 3 φ (φ.inverse t x)/φ.jacobian t (φ.inverse t x)^6 +
        15*Real.smoothTransition t^2*(iteratedDeriv 2 φ (φ.inverse t x))^3 /
          φ.jacobian t (φ.inverse t x)^7| ≤ 2592*ε := by
    calc
      _ ≤ |iteratedDeriv 4 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^5| +
          |10*Real.smoothTransition t*iteratedDeriv 2 φ (φ.inverse t x)*
            iteratedDeriv 3 φ (φ.inverse t x)/φ.jacobian t (φ.inverse t x)^6| +
          |15*Real.smoothTransition t^2*(iteratedDeriv 2 φ (φ.inverse t x))^3 /
            φ.jacobian t (φ.inverse t x)^7| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ = |iteratedDeriv 4 φ (φ.inverse t x)| / φ.jacobian t (φ.inverse t x)^5 +
          10*Real.smoothTransition t*|iteratedDeriv 2 φ (φ.inverse t x)| *
            |iteratedDeriv 3 φ (φ.inverse t x)|/φ.jacobian t (φ.inverse t x)^6 +
          15*Real.smoothTransition t^2*|iteratedDeriv 2 φ (φ.inverse t x)|^3 /
            φ.jacobian t (φ.inverse t x)^7 := by
        simp only [abs_div, abs_mul, abs_pow, abs_of_pos hJ0, abs_of_nonneg hb0]
        norm_num
      _ ≤ ε / (1/2:ℝ)^5 + 10*1*ε*ε/(1/2:ℝ)^6 +
          15*1^2*ε^3/(1/2:ℝ)^7 := by gcongr
      _ ≤ 2592*ε := by
        have he1 : ε ≤ 1 := by linarith
        have he2 : ε*ε ≤ ε := by nlinarith
        have he3 : ε^3 ≤ ε := by
          calc _ = ε*ε^2 := by ring
               _ ≤ ε*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hε he1) hε
               _ = ε := mul_one _
        norm_num
        nlinarith
  exact (mul_le_mul_of_nonneg_left hi (abs_nonneg _)).trans_eq (by ring)

lemma angularVelocity_iteratedDeriv (t x : ℝ) (k : ℕ) :
    iteratedDeriv k (φ.angularVelocity t) x =
      ((2*Real.pi)*((2*Real.pi)⁻¹)^k *
        iteratedDeriv k (φ.velocity t) (x/(2*Real.pi)) : ℝ) := by
  have hv : ContDiff ℝ ∞ (φ.velocity t) :=
    φ.velocity_smooth.comp (contDiff_const.prodMk contDiff_id)
  have hs : ContDiff ℝ ∞ (fun z => (2*Real.pi)*φ.velocity t (z/(2*Real.pi))) :=
    contDiff_const.mul (hv.comp (contDiff_id.div_const _))
  change iteratedDeriv k (fun z => (((2*Real.pi)*φ.velocity t (z/(2*Real.pi)) : ℝ) : ℂ)) x = _
  rw [RealCircleCalculus.iteratedDeriv_ofReal hs]
  dsimp only
  congr 1
  rw [iteratedDeriv_const_mul_field]
  have he : (fun z => φ.velocity t (z/(2*Real.pi))) =
      (fun z => φ.velocity t ((2*Real.pi)⁻¹*z)) := by funext z; congr 1; ring
  rw [he, iteratedDeriv_comp_const_mul (hv.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))]
  dsimp only
  rw [← mul_assoc]
  congr 2
  ring

lemma smoothTransition_deriv_bounded : ∃ B : ℝ, 0 < B ∧ ∀ t, |deriv Real.smoothTransition t| ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s := Icc (0:ℝ) 1)
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun t => ?_⟩
  by_cases ht : t ∈ Icc (0:ℝ) 1
  · exact (hB t ht).trans (le_max_right _ _)
  · have he : deriv Real.smoothTransition t = 0 := by
      rcases lt_or_ge t 0 with h | h
      · have hh : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
          filter_upwards [Iio_mem_nhds h] with s hs
          exact Real.smoothTransition.zero_of_nonpos hs.le
        rw [hh.deriv_eq, deriv_const]
      · have h1 : 1 < t := lt_of_not_ge (fun h1 => ht ⟨h,h1⟩)
        have hh : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
          filter_upwards [Ioi_mem_nhds h1] with s hs
          exact Real.smoothTransition.one_of_one_le hs.le
        rw [hh.deriv_eq, deriv_const]
    rw [he, abs_zero]
    exact zero_le_one.trans (le_max_left _ _)

 

theorem angularStressPath_small_near_identity :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : SmoothLift) (ε : ℝ), 0 ≤ ε → ε ≤ 1/2 →
      (∀ x, |φ x-x| ≤ ε) → (∀ x, |deriv φ x-1| ≤ ε) →
      (∀ k ∈ Finset.Icc 2 4, ∀ x, |iteratedDeriv k φ x| ≤ ε) →
      ∀ t, coefficientSeminorm (φ.angularStressPath.coefficients t) 2 ≤ C*ε := by
  obtain ⟨B, hB, hβ⟩ := smoothTransition_deriv_bounded
  let K : ℝ := (2*Real.pi)*2592*B
  let S : ℝ := ∑' n : ℤ, ((1+|(n:ℝ)|)^2)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have hS : 0 ≤ S := tsum_nonneg (fun n => by positivity)
  refine ⟨16*K*(1+S), by positivity, fun φ ε hε hε1 h0 h1 hk t => ?_⟩
  have hv (x : ℝ) : |φ.velocity t x| ≤ B*ε := by
    dsimp only [velocity]
    rw [abs_mul]
    exact mul_le_mul (hβ t) (h0 _) (abs_nonneg _) hB.le
  have h0' (x : ℝ) : ‖φ.angularVelocity t x‖ ≤ K*ε := by
    change ‖(((2*Real.pi)*φ.velocity t (x/(2*Real.pi)) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    calc _ ≤ (2*Real.pi)*(B*ε) := mul_le_mul_of_nonneg_left (hv _) (by positivity)
         _ ≤ K*ε := by dsimp only [K]; nlinarith [mul_nonneg hB.le hε, Real.pi_pos]
  have h4' (x : ℝ) : ‖iteratedDeriv 4 (φ.angularVelocity t) x‖ ≤ K*ε := by
    rw [φ.angularVelocity_iteratedDeriv, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), abs_pow,
      abs_of_pos (by positivity : (0:ℝ) < (2*Real.pi)⁻¹)]
    have hpi : (2*Real.pi)⁻¹ ≤ (1:ℝ) := by
      apply (inv_le_one₀ (by positivity)).mpr
      linarith [Real.pi_gt_three]
    calc
      _ ≤ (2*Real.pi)*1*(2592*B*ε) := by
        gcongr
        · exact pow_le_one₀ (by positivity) hpi
        · exact (φ.velocity_fourth_bound hε hε1 h1 hk _ _).trans (by gcongr; exact hβ t)
      _ = K*ε := by dsimp [K]; ring
  have hc (n : ℤ) := (φ.angularVelocity t).coefficient_summable_bound 2
    (mul_nonneg hK.le hε) (fun x _ => h0' x) (fun x _ => h4' x) n
  change (∑' n : ℤ, ‖(φ.angularVelocity t).coefficient n‖*(1+|(n:ℝ)|)^2) ≤ _
  calc
    _ ≤ ∑' n : ℤ, (2^(2+2)*(K*ε))*((1+|(n:ℝ)|)^2)⁻¹ :=
      Summable.tsum_le_tsum hc ((φ.angularVelocity t).rapid_coefficients 2)
        (summable_circle_decay.mul_left _)
    _ = 16*K*S*ε := by rw [tsum_mul_left]; dsimp only [S]; ring
    _ ≤ 16*K*(1+S)*ε := by gcongr; linarith

end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

end

end OAI
