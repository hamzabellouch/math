import OAI.Topology.CoarseAssembly.CayleyNaturality
import OAI.Topology.CoarseAssembly.FredholmModule

namespace OAI

/-! # The rational boundary respects bounded intertwiners

This includes restriction to a component of a Hilbert direct sum. No
multiplicativity of compression on arbitrary operators is assumed.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem cayleyDenominator_intertwines (R : H →L[ℂ] K) (F : H →L[ℂ] H) (G : K →L[ℂ] K)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (h : ∀ x, R (F x) = G (R x)) (x : H) :
    R ((cayleyDenominator F hF : H →L[ℂ] H) x) =
      (cayleyDenominator G hG : K →L[ℂ] K) (R x) := by
  simp only [cayleyDenominator_val, Algebra.algebraMap_eq_smul_one,
    add_apply, smul_apply,
    one_apply_eq_self, map_add, map_smul, h]

theorem cayleyDenominator_inv_intertwines (R : H →L[ℂ] K) (F : H →L[ℂ] H) (G : K →L[ℂ] K)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (h : ∀ x, R (F x) = G (R x)) (x : H) :
    R ((↑(cayleyDenominator F hF)⁻¹ : H →L[ℂ] H) x) =
      (↑(cayleyDenominator G hG)⁻¹ : K →L[ℂ] K) (R x) := by
  let b := cayleyDenominator F hF
  let d := cayleyDenominator G hG
  have hleft (y : K) : (↑d⁻¹ : K →L[ℂ] K) ((d : K →L[ℂ] K) y) = y := by
    change ((↑d⁻¹ : K →L[ℂ] K) * (d : K →L[ℂ] K)) y = y
    rw [Units.inv_mul, one_apply_eq_self]
  have hright (y : H) : (b : H →L[ℂ] H) ((↑b⁻¹ : H →L[ℂ] H) y) = y := by
    change ((b : H →L[ℂ] H) * (↑b⁻¹ : H →L[ℂ] H)) y = y
    rw [Units.mul_inv, one_apply_eq_self]
  calc
    R ((↑b⁻¹ : H →L[ℂ] H) x) = (↑d⁻¹ : K →L[ℂ] K) ((d : K →L[ℂ] K) (R ((↑b⁻¹ : H →L[ℂ] H) x))) :=
      (hleft _).symm
    _ = (↑d⁻¹ : K →L[ℂ] K) (R ((b : H →L[ℂ] H) ((↑b⁻¹ : H →L[ℂ] H) x))) := by
      rw [cayleyDenominator_intertwines R F G hF hG h]
    _ = (↑d⁻¹ : K →L[ℂ] K) (R x) := by rw [hright]

theorem cayleyUnitary_intertwines (R : H →L[ℂ] K) (F : H →L[ℂ] H) (G : K →L[ℂ] K)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (h : ∀ x, R (F x) = G (R x)) (x : H) :
    R ((cayleyUnitary F hF : H →L[ℂ] H) x) = (cayleyUnitary G hG : K →L[ℂ] K) (R x) := by
  simp only [cayleyUnitary_val, cayleyDenominator_star,
    Algebra.algebraMap_eq_smul_one, mul_apply_eq_comp,
    sub_apply, smul_apply,
    one_apply_eq_self, map_sub, map_smul, h]
  rw [cayleyDenominator_inv_intertwines R F G hF hG h]

theorem rationalBoundaryUnitary_intertwines (R : H →L[ℂ] K)
    (F : H →L[ℂ] H) (G : K →L[ℂ] K) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (h : ∀ x, R (F x) = G (R x)) (x : H) :
    R ((rationalBoundaryUnitary F hF : H →L[ℂ] H) x) =
      (rationalBoundaryUnitary G hG : K →L[ℂ] K) (R x) := by
  simp only [rationalBoundaryUnitary, Unitary.coe_neg, Submonoid.coe_mul,
    neg_apply, mul_apply_eq_comp, map_neg]
  rw [cayleyUnitary_intertwines R F G hF hG h,
    cayleyUnitary_intertwines R F G hF hG h]

end CoarseAssembly.Analytic

end

end OAI
