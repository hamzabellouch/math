import OAI.Topology.CoarseAssembly.CayleyUnitization

namespace OAI

/-! # Naturality for identity-extended nonunital homomorphisms -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def nonunitalIdentityExtension (φ : A →⋆ₙₐ[ℂ] B) (F : A) : B := 1 + φ (F - 1)

theorem nonunitalIdentityExtension_selfAdjoint (φ : A →⋆ₙₐ[ℂ] B)
    (F : A) (hF : IsSelfAdjoint F) : IsSelfAdjoint (nonunitalIdentityExtension φ F) :=
  (IsSelfAdjoint.one B).add ((hF.sub (IsSelfAdjoint.one A)).map φ)

theorem starLift_inr (φ : A →⋆ₙₐ[ℂ] B) (a : A) :
    Unitization.starLift φ (a : Unitization ℂ A) = φ a := by
  change algebraMap ℂ B 0 + φ a = φ a
  rw [map_zero, zero_add]

theorem starLift_identityUnitization (φ : A →⋆ₙₐ[ℂ] B) (F : A) :
    Unitization.starLift φ (identityUnitization F) = nonunitalIdentityExtension φ F := by
  change Unitization.starLift φ (1 + ((F - 1 : A) : Unitization ℂ A)) = 1 + φ (F - 1)
  rw [map_add, map_one, starLift_inr]

theorem nonunital_rationalBoundaryUnitary (φ : A →⋆ₙₐ[ℂ] B)
    (F : A) (hF : IsSelfAdjoint F) :
    1 + φ ((rationalBoundaryUnitary F hF : A) - 1) =
      (rationalBoundaryUnitary (nonunitalIdentityExtension φ F)
        (nonunitalIdentityExtension_selfAdjoint φ F hF) : B) := by
  have h := map_rationalBoundaryUnitary (Unitization.starLift φ)
    (identityUnitization F) (identityUnitization_selfAdjoint F hF)
  rw [rationalBoundaryUnitary_identity F hF] at h
  simpa only [map_add, map_one, starLift_inr, starLift_identityUnitization] using h

end CoarseAssembly.Analytic

end

end OAI
