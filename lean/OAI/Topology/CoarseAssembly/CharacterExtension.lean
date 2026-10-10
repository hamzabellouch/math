import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.ExplicitCutDown
import Mathlib.Algebra.Star.StarProjection

namespace OAI

/-! # Completing a represented subspace using a character

For a unital coefficient algebra with a character, the complement of the
represented subspace can carry that character. The cut-down operator acts
as the identity there, so this completion preserves the Fredholm defects.
-/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A] {H : HilbertSpace}

def characterProjectionRepresentation (χ : A →⋆ₐ[ℂ] ℂ) (P : End H)
    (hP : IsStarProjection P) : A →⋆ₙₐ[ℂ] End H where
  toFun a := χ a • P
  map_zero' := by simp
  map_add' a b := by simp [add_smul]
  map_mul' a b := by
    have hPP : P * P = P := hP.isIdempotentElem
    rw [map_mul, smul_mul_assoc, mul_smul_comm, hPP, smul_smul, mul_comm]
  map_smul' z a := by simp [smul_smul]
  map_star' a := by rw [map_star, star_smul, hP.isSelfAdjoint.star_eq]

theorem representation_unit_projection (c : OddCycle A) :
    IsStarProjection (c.representation 1) :=
  ⟨representation_unit_sq c, representation_unit_selfAdjoint c⟩

theorem representation_complement_right (c : OddCycle A) (a : A) :
    c.representation a * (1 - c.representation 1) = 0 := by
  rw [mul_sub, mul_one, ← map_mul, mul_one, sub_self]

theorem representation_complement_left (c : OddCycle A) (a : A) :
    (1 - c.representation 1) * c.representation a = 0 := by
  rw [sub_mul, one_mul, ← map_mul, one_mul, sub_self]

@[simp] theorem completedRepresentation_apply (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) (a : A) :
    completedRepresentation c χ a = c.representation a + χ a • (1 - c.representation 1) := rfl

theorem completedRepresentation_one (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    completedRepresentation c χ 1 = 1 := by
  simp only [completedRepresentation_apply, map_one, one_smul]
  abel

/-- Any representation with the identity operator is degenerate. -/
def identityOperatorCycle (ρ : A →⋆ₙₐ[ℂ] End H) : OddCycle A where
  space := H
  representation := ρ
  operator := 1
  commutator_compact _ := by simp; exact isCompactOperator_zero
  square_compact _ := by simp; exact isCompactOperator_zero
  adjoint_compact _ := by simp; exact isCompactOperator_zero

theorem identityOperatorCycle_degenerate (ρ : A →⋆ₙₐ[ℂ] End H) :
    (identityOperatorCycle ρ).Degenerate := by
  constructor
  · intro a; change (1 : End H) * ρ a - ρ a * 1 = 0; simp
  constructor
  · intro a; change ((1 : End H) * 1 - 1) * ρ a = 0; simp
  · intro a; change (star (1 : End H) - 1) * ρ a = 0; simp

theorem characterExtension_unital (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ)
    (hF : IsSelfAdjoint c.operator)
    (hQ : c.operator * (1 - c.representation 1) = 1 - c.representation 1)
    (hsq : IsCompactOperator (c.operator * c.operator - 1 : End c.space)) :
    (c.characterExtension χ hF hQ hsq).representation 1 = 1 :=
  completedRepresentation_one c χ

end CoarseAssembly.Analytic

end

end OAI
