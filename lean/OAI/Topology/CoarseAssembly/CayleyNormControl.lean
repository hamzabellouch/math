import OAI.Topology.CoarseAssembly.CayleyBoundary

namespace OAI

/-! # A uniform Lipschitz estimate for the rational boundary unitary -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem cayleyDenominator_inverse_identity (F : A) (hF : IsSelfAdjoint F) :
    (2 * Complex.I : ℂ) • (↑(cayleyDenominator F hF)⁻¹ : A) =
      1 - (cayleyUnitary F hF : A) := by
  have hscalar : algebraMap ℂ A (2 * Complex.I) =
      (cayleyDenominator F hF : A) - star (cayleyDenominator F hF : A) := by
    rw [cayleyDenominator_star, cayleyDenominator_val, map_mul]
    simp only [map_ofNat]
    noncomm_ring
  rw [Algebra.smul_def, hscalar, sub_mul, Units.mul_inv, cayleyUnitary_val]

theorem cayleyDenominator_inverse_norm_le (F : A) (hF : IsSelfAdjoint F) :
    ‖(↑(cayleyDenominator F hF)⁻¹ : A)‖ ≤ 1 := by
  nontriviality A
  have h := norm_sub_le (1 : A) (cayleyUnitary F hF : A)
  rw [← cayleyDenominator_inverse_identity F hF, norm_smul, norm_mul,
    Complex.norm_I, norm_one, CStarRing.norm_coe_unitary] at h
  norm_num at h
  linarith

theorem cayleyDenominator_inverse_sub_norm_le (F G : A)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    ‖(↑(cayleyDenominator F hF)⁻¹ : A) - ↑(cayleyDenominator G hG)⁻¹‖ ≤ ‖F - G‖ := by
  let u := cayleyDenominator F hF
  let v := cayleyDenominator G hG
  have he : (↑u⁻¹ : A) - ↑v⁻¹ = ↑u⁻¹ * (G - F) * ↑v⁻¹ := by
    have hdiff : G - F = (v : A) - u := by
      simp only [u, v, cayleyDenominator_val, add_sub_add_right_eq_sub]
    rw [hdiff, mul_sub, sub_mul]
    rw [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul, one_mul]
  rw [he]
  calc
    _ ≤ ‖(↑u⁻¹ : A)‖ * ‖G - F‖ * ‖(↑v⁻¹ : A)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖G - F‖ * 1 := by
      gcongr
      · exact cayleyDenominator_inverse_norm_le F hF
      · exact cayleyDenominator_inverse_norm_le G hG
    _ = ‖F - G‖ := by rw [one_mul, mul_one, norm_sub_rev]

theorem cayleyUnitary_sub_norm_le (F G : A) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    ‖(cayleyUnitary F hF : A) - cayleyUnitary G hG‖ ≤ 2 * ‖F - G‖ := by
  have he : (cayleyUnitary F hF : A) - cayleyUnitary G hG =
      -(2 * Complex.I : ℂ) •
        ((↑(cayleyDenominator F hF)⁻¹ : A) - ↑(cayleyDenominator G hG)⁻¹) := by
    rw [neg_smul, smul_sub, cayleyDenominator_inverse_identity,
      cayleyDenominator_inverse_identity]
    abel
  rw [he, norm_smul, norm_neg, norm_mul, Complex.norm_I]
  norm_num only [Complex.norm_ofNat, mul_one]
  exact mul_le_mul_of_nonneg_left (cayleyDenominator_inverse_sub_norm_le F G hF hG) (by norm_num)

theorem rationalBoundaryUnitary_sub_norm_le (F G : A)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    ‖(rationalBoundaryUnitary F hF : A) - rationalBoundaryUnitary G hG‖ ≤ 4 * ‖F - G‖ := by
  nontriviality A
  let u : A := cayleyUnitary F hF
  let v : A := cayleyUnitary G hG
  have hu : ‖u‖ = 1 := CStarRing.norm_coe_unitary _
  have hv : ‖v‖ = 1 := CStarRing.norm_coe_unitary _
  have he : -(u * u) - -(v * v) = (v - u) * v + u * (v - u) := by
    rw [neg_sub_neg, sub_mul, mul_sub, sub_add_sub_cancel]
  change ‖-(u * u) - -(v * v)‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖(v - u) * v‖ + ‖u * (v - u)‖ := norm_add_le _ _
    _ ≤ ‖v - u‖ * ‖v‖ + ‖u‖ * ‖v - u‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖u - v‖ := by rw [hu, hv, norm_sub_rev]; ring
    _ ≤ 2 * (2 * ‖F - G‖) := mul_le_mul_of_nonneg_left (cayleyUnitary_sub_norm_le F G hF hG) (by norm_num)
    _ = _ := by ring

end CoarseAssembly.Analytic

end

end OAI
