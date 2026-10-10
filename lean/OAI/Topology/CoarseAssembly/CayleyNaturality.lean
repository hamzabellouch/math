import OAI.Topology.CoarseAssembly.CayleyBoundary

namespace OAI

/-! # Naturality of the rational boundary formula -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem map_cayleyDenominator (φ : A →⋆ₐ[ℂ] B) (F : A) (hF : IsSelfAdjoint F) :
    Units.map φ.toMonoidHom (cayleyDenominator F hF) =
      cayleyDenominator (φ F) (hF.map φ) := by
  apply Units.ext
  change φ (cayleyDenominator F hF : A) =
    (cayleyDenominator (φ F) (hF.map φ) : B)
  simp only [cayleyDenominator_val, map_add]
  congr 1
  exact φ.commutes Complex.I

theorem map_cayleyUnitary (φ : A →⋆ₐ[ℂ] B) (F : A) (hF : IsSelfAdjoint F) :
    φ (cayleyUnitary F hF : A) = (cayleyUnitary (φ F) (hF.map φ) : B) := by
  have hi := congrArg (fun u : Bˣ => (↑(u⁻¹) : B)) (map_cayleyDenominator φ F hF)
  change φ (↑(cayleyDenominator F hF)⁻¹ : A) =
    (↑(cayleyDenominator (φ F) (hF.map φ))⁻¹ : B) at hi
  simp only [cayleyUnitary_val, map_mul, map_star, hi]
  congr 2
  exact congrArg (fun u : Bˣ => (u : B)) (map_cayleyDenominator φ F hF)

theorem map_rationalBoundaryUnitary (φ : A →⋆ₐ[ℂ] B) (F : A) (hF : IsSelfAdjoint F) :
    φ (rationalBoundaryUnitary F hF : A) =
      (rationalBoundaryUnitary (φ F) (hF.map φ) : B) := by
  simp only [rationalBoundaryUnitary, Unitary.coe_neg, Submonoid.coe_mul, map_neg, map_mul,
    map_cayleyUnitary]

end CoarseAssembly.Analytic

end

end OAI
