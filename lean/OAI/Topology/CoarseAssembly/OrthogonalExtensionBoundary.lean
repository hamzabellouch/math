import OAI.Topology.CoarseAssembly.OrthogonalSumBoundary

namespace OAI

/-! # Additivity for orthogonal corners with an unused complementary summand -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]

def nonunitalOrthogonalSumHom (φ : A →⋆ₙₐ[ℂ] R) (ψ : B →⋆ₙₐ[ℂ] R)
    (horth : ∀ a b, φ a * ψ b = 0) : A × B →⋆ₙₐ[ℂ] R where
  toFun p := φ p.1 + ψ p.2
  map_zero' := by simp
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, add_mul, mul_add,
      horth, orthogonal_maps_reverse φ ψ horth, add_zero, zero_add]
  map_smul' z p := by
    change φ (z • p.1) + ψ (z • p.2) = z • (φ p.1 + ψ p.2)
    rw [map_smul, map_smul, smul_add]
  map_star' p := by simp only [Prod.fst_star, Prod.snd_star, map_star, star_add]

theorem nonunitalUnitaryExtension_orthogonal (φ : A →⋆ₙₐ[ℂ] R) (ψ : B →⋆ₙₐ[ℂ] R)
    (horth : ∀ a b, φ a * ψ b = 0) (u : unitary A) (v : unitary B) :
    ((nonunitalUnitaryExtension φ u * nonunitalUnitaryExtension ψ v : unitary R) : R) =
      1 + φ ((u : A) - 1) + ψ ((v : B) - 1) := by
  change (1 + φ ((u : A) - 1)) * (1 + ψ ((v : B) - 1)) = _
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, horth, add_zero]
  noncomm_ring

theorem rationalBoundaryUnitary_orthogonalExtension
    (φ : A →⋆ₙₐ[ℂ] R) (ψ : B →⋆ₙₐ[ℂ] R) (horth : ∀ a b, φ a * ψ b = 0)
    (F : A) (G : B) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    rationalBoundaryUnitary (nonunitalIdentityExtension (nonunitalOrthogonalSumHom φ ψ horth) (F, G))
      (nonunitalIdentityExtension_selfAdjoint _ _ (Prod.ext hF.star_eq hG.star_eq)) =
    nonunitalUnitaryExtension φ (rationalBoundaryUnitary F hF) *
      nonunitalUnitaryExtension ψ (rationalBoundaryUnitary G hG) := by
  have hp : IsSelfAdjoint (F, G) := Prod.ext hF.star_eq hG.star_eq
  have h := nonunital_rationalBoundaryUnitary (nonunitalOrthogonalSumHom φ ψ horth) (F, G) hp
  have hfst := map_rationalBoundaryUnitary (StarAlgHom.fst ℂ A B) (F, G) hp
  have hsnd := map_rationalBoundaryUnitary (StarAlgHom.snd ℂ A B) (F, G) hp
  change (rationalBoundaryUnitary (F, G) hp : A × B).1 = (rationalBoundaryUnitary F hF : A) at hfst
  change (rationalBoundaryUnitary (F, G) hp : A × B).2 = (rationalBoundaryUnitary G hG : B) at hsnd
  apply Subtype.ext
  rw [nonunitalUnitaryExtension_orthogonal φ ψ horth]
  change 1 + (φ ((rationalBoundaryUnitary (F, G) hp : A × B).1 - 1) +
    ψ ((rationalBoundaryUnitary (F, G) hp : A × B).2 - 1)) = _ at h
  rw [hfst, hsnd] at h
  simpa only [add_assoc] using h.symm

end CoarseAssembly.Analytic

end

end OAI
