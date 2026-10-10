import OAI.Topology.CoarseAssembly.BoundedTransform

namespace OAI

/-! # The bounded transform changes a unital Fredholm operator compactly -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

theorem cayleyDenominator_normSquare (F : A) (hF : IsSelfAdjoint F) :
    (cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A) = F * F + 1 := by
  rw [cayleyDenominator_star, cayleyDenominator_val]
  have hi : algebraMap ℂ A Complex.I * algebraMap ℂ A Complex.I = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have hc := Algebra.commutes (R := ℂ) (A := A) Complex.I F
  noncomm_ring [hc, hi]

theorem cayleyUnitary_mul_normSquare (F : A) (hF : IsSelfAdjoint F) :
    (cayleyUnitary F hF : A) *
      ((cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A)) =
      star (cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A) := by
  rw [cayleyUnitary_val]
  calc
    _ = star (cayleyDenominator F hF : A) *
        (((↑(cayleyDenominator F hF)⁻¹ : A) * (cayleyDenominator F hF : A)) *
          star (cayleyDenominator F hF : A)) := by noncomm_ring
    _ = _ := by rw [Units.inv_mul, one_mul]

theorem star_cayleyUnitary_mul_normSquare (F : A) (hF : IsSelfAdjoint F) :
    star (cayleyUnitary F hF : A) *
      ((cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A)) =
      (cayleyDenominator F hF : A) * (cayleyDenominator F hF : A) := by
  let b := cayleyDenominator F hF
  have hc : Commute (b : A) (star (b : A)) := (cayleyDenominator_normal F hF).symm
  rw [cayleyUnitary_val, star_mul, star_star, ← Units.coe_star_inv]
  change ((↑(star b)⁻¹ : A) * (b : A)) * ((b : A) * star (b : A)) = (b : A) * (b : A)
  calc
    _ = (↑(star b)⁻¹ : A) * ((b : A) * ((b : A) * star (b : A))) := by noncomm_ring
    _ = (↑(star b)⁻¹ : A) * ((b : A) * (star (b : A) * (b : A))) := by rw [hc.eq]
    _ = (↑(star b)⁻¹ : A) * (((b : A) * star (b : A)) * (b : A)) := by noncomm_ring
    _ = (↑(star b)⁻¹ : A) * ((star (b : A) * (b : A)) * (b : A)) := by rw [hc.eq]
    _ = ((↑(star b)⁻¹ : A) * star (b : A)) * ((b : A) * (b : A)) := by noncomm_ring
    _ = _ := by rw [← Units.coe_star, Units.inv_mul, one_mul]

theorem boundedTransform_mul_normSquare (F : A) (hF : IsSelfAdjoint F) :
    boundedTransform F hF *
      ((cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A)) = (2 : ℂ) • F := by
  unfold boundedTransform
  rw [smul_mul_assoc, sub_mul, cayleyUnitary_mul_normSquare, star_cayleyUnitary_mul_normSquare]
  have hp : star (cayleyDenominator F hF : A) * star (cayleyDenominator F hF : A) -
      (cayleyDenominator F hF : A) * (cayleyDenominator F hF : A) =
      (-4 * Complex.I : ℂ) • F := by
    rw [cayleyDenominator_star, cayleyDenominator_val, Algebra.smul_def]
    simp only [map_mul, map_neg, map_ofNat]
    have hc := Algebra.commutes (R := ℂ) (A := A) Complex.I F
    noncomm_ring [hc]
  rw [hp, smul_smul]
  have hs : (Complex.I / 2) * (-4 * Complex.I) = (2 : ℂ) := by
    calc
      _ = -2 * (Complex.I * Complex.I) := by ring
      _ = 2 := by rw [Complex.I_mul_I]; norm_num
  rw [hs]

theorem boundedTransform_eq_of_involution (F : A) (hF : IsSelfAdjoint F) (hsq : F * F = 1) :
    boundedTransform F hF = F := by
  have hh := boundedTransform_mul_normSquare F hF
  rw [cayleyDenominator_normSquare, hsq, mul_add, mul_one] at hh
  have he : (2 : ℂ) • boundedTransform F hF = (2 : ℂ) • F := by
    simpa only [two_smul] using hh
  exact (smul_right_injective A (by norm_num : (2 : ℂ) ≠ 0)) he

variable {H : HilbertSpace}

theorem boundedTransform_sub_compact (F : End H) (hF : IsSelfAdjoint F)
    (hK : IsCompactOperator (F * F - 1 : End H)) :
    IsCompactOperator (boundedTransform F hF - F : End H) := by
  let b := cayleyDenominator F hF
  have hm : IsCompactOperator ((boundedTransform F hF - F) * ((b : End H) * star (b : End H))) := by
    rw [sub_mul, boundedTransform_mul_normSquare, cayleyDenominator_normSquare]
    have he : (2 : ℂ) • F - F * (F * F + 1) = -(F * (F * F - 1)) := by
      rw [Algebra.smul_def]
      simp only [map_ofNat]
      noncomm_ring
    rw [he]
    exact (compact_mul_left hK F).neg
  let v : (End H)ˣ := b * star b
  change IsCompactOperator ((boundedTransform F hF - F) * (v : End H)) at hm
  have hn := compact_mul_right hm (↑v⁻¹ : End H)
  rwa [mul_assoc, Units.mul_inv, mul_one] at hn

end CoarseAssembly.Analytic

end

end OAI
