import OAI.Topology.CoarseAssembly.NonunitalUnitaryExtension
import OAI.Topology.CoarseAssembly.RelativeMultiplication

namespace OAI

/-! # The boundary of an orthogonal sum is the product of its two boundaries -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]

variable (φ : A →⋆ₙₐ[ℂ] R) (ψ : B →⋆ₙₐ[ℂ] R)
  (horth : ∀ a b, φ a * ψ b = 0) (hone : φ 1 + ψ 1 = 1)

include horth in
theorem orthogonal_maps_reverse (a : A) (b : B) : ψ b * φ a = 0 := by
  have h := congrArg star (horth (star a) (star b))
  simpa only [star_mul, ← map_star, star_star, star_zero] using h

def orthogonalSumHom : A × B →⋆ₐ[ℂ] R where
  toFun p := φ p.1 + ψ p.2
  map_zero' := by simp
  map_one' := hone
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, add_mul, mul_add,
      horth, orthogonal_maps_reverse φ ψ horth, add_zero, zero_add]
  commutes' z := by
    change φ (algebraMap ℂ A z) + ψ (algebraMap ℂ B z) = algebraMap ℂ R z
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, ← smul_add, hone]
  map_star' p := by simp only [Prod.fst_star, Prod.snd_star, map_star, star_add]

include horth hone in
theorem nonunitalUnitaryExtension_product (u : unitary A) (v : unitary B) :
    ((nonunitalUnitaryExtension φ u * nonunitalUnitaryExtension ψ v : unitary R) : R) =
      φ (u : A) + ψ (v : B) := by
  change (1 + φ ((u : A) - 1)) * (1 + ψ ((v : B) - 1)) = _
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, horth, add_zero]
  rw [map_sub, map_sub, ← hone]
  noncomm_ring

theorem orthogonalSum_selfAdjoint (F : A) (G : B) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    IsSelfAdjoint (φ F + ψ G) := (hF.map φ).add (hG.map ψ)

include horth hone in
theorem rationalBoundaryUnitary_orthogonalSum (F : A) (G : B)
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G) :
    rationalBoundaryUnitary (φ F + ψ G) (orthogonalSum_selfAdjoint φ ψ F G hF hG) =
      nonunitalUnitaryExtension φ (rationalBoundaryUnitary F hF) *
        nonunitalUnitaryExtension ψ (rationalBoundaryUnitary G hG) := by
  have hp : IsSelfAdjoint (F, G) := Prod.ext hF.star_eq hG.star_eq
  have h := map_rationalBoundaryUnitary (orthogonalSumHom φ ψ horth hone) (F, G) hp
  have hfst := map_rationalBoundaryUnitary (StarAlgHom.fst ℂ A B) (F, G) hp
  have hsnd := map_rationalBoundaryUnitary (StarAlgHom.snd ℂ A B) (F, G) hp
  apply Subtype.ext
  rw [nonunitalUnitaryExtension_product φ ψ horth hone]
  change φ (rationalBoundaryUnitary (F, G) hp : A × B).1 +
      ψ (rationalBoundaryUnitary (F, G) hp : A × B).2 = _ at h
  change (rationalBoundaryUnitary (F, G) hp : A × B).1 = _ at hfst
  change (rationalBoundaryUnitary (F, G) hp : A × B).2 = _ at hsnd
  rw [hfst, hsnd] at h
  exact h.symm

end CoarseAssembly.Analytic

namespace CoarseAssembly.OperatorKTheory

open Analytic

variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]

/-- The exact orthogonal-sum formula gives addition in the existing K₁ group. -/
theorem relativeClass_orthogonalSum (S : NonUnitalStarSubalgebra ℂ R)
    [hS : IsClosed (S : Set R)]
    (φ : A →⋆ₙₐ[ℂ] R) (ψ : B →⋆ₙₐ[ℂ] R)
    (horth : ∀ a b, φ a * ψ b = 0) (hone : φ 1 + ψ 1 = 1)
    (F : A) (G : B) (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (hsum : (rationalBoundaryUnitary (φ F + ψ G)
      (orthogonalSum_selfAdjoint φ ψ F G hF hG) : R) - 1 ∈ S)
    (hleft : (rationalBoundaryUnitary (nonunitalIdentityExtension φ F)
      (nonunitalIdentityExtension_selfAdjoint φ F hF) : R) - 1 ∈ S)
    (hright : (rationalBoundaryUnitary (nonunitalIdentityExtension ψ G)
      (nonunitalIdentityExtension_selfAdjoint ψ G hG) : R) - 1 ∈ S) :
    relativeClass S (rationalBoundaryUnitary (φ F + ψ G)
      (orthogonalSum_selfAdjoint φ ψ F G hF hG)) hsum =
    relativeClass S (rationalBoundaryUnitary (nonunitalIdentityExtension φ F)
      (nonunitalIdentityExtension_selfAdjoint φ F hF)) hleft +
    relativeClass S (rationalBoundaryUnitary (nonunitalIdentityExtension ψ G)
      (nonunitalIdentityExtension_selfAdjoint ψ G hG)) hright := by
  have hu := rationalBoundaryUnitary_orthogonalSum φ ψ horth hone F G hF hG
  rw [nonunitalUnitaryExtension_boundary, nonunitalUnitaryExtension_boundary] at hu
  have h := relativeClass_mul S
    (rationalBoundaryUnitary (nonunitalIdentityExtension φ F)
      (nonunitalIdentityExtension_selfAdjoint φ F hF))
    (rationalBoundaryUnitary (nonunitalIdentityExtension ψ G)
      (nonunitalIdentityExtension_selfAdjoint ψ G hG)) hleft hright
  simpa only [← hu] using h

end CoarseAssembly.OperatorKTheory

end

end OAI
