import OAI.Topology.CoarseAssembly.CayleyNonunitalNaturality

namespace OAI

/-! # Identity extension of an arbitrary unitary under a nonunital map -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def nonunitalUnitaryExtension (φ : A →⋆ₙₐ[ℂ] B) (u : unitary A) : unitary B := by
  have hl : star (u : A) * (u : A) = 1 := Unitary.coe_star_mul_self u
  have hr : (u : A) * star (u : A) = 1 := by
    have h := Unitary.coe_mul_star_self u
    change (u : A) * star (u : A) = 1 at h
    exact h
  have hl' : ((u : A) - 1) + star ((u : A) - 1) +
      star ((u : A) - 1) * ((u : A) - 1) = 0 := by
    rw [star_sub, star_one]
    noncomm_ring [hl]
  have hr' : star ((u : A) - 1) + ((u : A) - 1) +
      ((u : A) - 1) * star ((u : A) - 1) = 0 := by
    rw [star_sub, star_one]
    noncomm_ring [hr]
  refine ⟨1 + φ ((u : A) - 1), ?_, ?_⟩
  · change star (1 + φ ((u : A) - 1)) * (1 + φ ((u : A) - 1)) = 1
    calc
      _ = 1 + φ (((u : A) - 1) + star ((u : A) - 1) +
        star ((u : A) - 1) * ((u : A) - 1)) := by
          rw [map_add, map_add, map_mul, map_star, star_add, star_one]
          noncomm_ring
      _ = 1 := by rw [hl', map_zero, add_zero]
  · change (1 + φ ((u : A) - 1)) * star (1 + φ ((u : A) - 1)) = 1
    calc
      _ = 1 + φ (star ((u : A) - 1) + ((u : A) - 1) +
        ((u : A) - 1) * star ((u : A) - 1)) := by
          rw [map_add, map_add, map_mul, map_star, star_add, star_one]
          noncomm_ring
      _ = 1 := by rw [hr', map_zero, add_zero]

@[simp] theorem nonunitalUnitaryExtension_val (φ : A →⋆ₙₐ[ℂ] B) (u : unitary A) :
    (nonunitalUnitaryExtension φ u : B) = 1 + φ ((u : A) - 1) := rfl

theorem nonunitalUnitaryExtension_boundary (φ : A →⋆ₙₐ[ℂ] B)
    (F : A) (hF : IsSelfAdjoint F) :
    nonunitalUnitaryExtension φ (rationalBoundaryUnitary F hF) =
      rationalBoundaryUnitary (nonunitalIdentityExtension φ F)
        (nonunitalIdentityExtension_selfAdjoint φ F hF) := by
  apply Subtype.ext
  exact nonunital_rationalBoundaryUnitary φ F hF

end CoarseAssembly.Analytic

end

end OAI
