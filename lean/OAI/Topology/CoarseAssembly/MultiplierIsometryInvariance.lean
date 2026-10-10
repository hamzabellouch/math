import OAI.Topology.CoarseAssembly.RelativeIsometry
import OAI.Topology.CoarseAssembly.MultiplierUnitaryHomotopy
import OAI.Topology.CoarseAssembly.CayleyNonunitalNaturality

namespace OAI

/-! # The Roe boundary is invariant under multiplier isometries -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem nonunitalIdentityExtension_square_defect (φ : A →⋆ₙₐ[ℂ] B) (F : A) :
    nonunitalIdentityExtension φ F ^ 2 - 1 = φ (F ^ 2 - 1) := by
  calc
    _ = φ ((F - 1) + (F - 1) + (F - 1) * (F - 1)) := by
      rw [map_add, map_add, map_mul]
      dsimp only [nonunitalIdentityExtension]
      noncomm_ring
    _ = _ := congrArg φ (by noncomm_ring)

end CoarseAssembly.Analytic

namespace CoarseAssembly.DiscreteRoe

open Analytic OperatorKTheory

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def isometricMultiplier (V : multiplierAlgebra (X := X) (H := H))
    (hV : star V * V = 1) (F : multiplierAlgebra (X := X) (H := H)) :
    multiplierAlgebra (X := X) (H := H) :=
  nonunitalIdentityExtension (isometryCornerHom V hV) F

theorem isometricMultiplier_selfAdjoint (V : multiplierAlgebra (X := X) (H := H))
    (hV : star V * V = 1) (F : multiplierAlgebra (X := X) (H := H))
    (hF : IsSelfAdjoint F) : IsSelfAdjoint (isometricMultiplier V hV F) :=
  nonunitalIdentityExtension_selfAdjoint _ F hF

theorem isometricMultiplier_defect_mem (V : multiplierAlgebra (X := X) (H := H))
    (hV : star V * V = 1) (F : multiplierAlgebra (X := X) (H := H))
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    (isometricMultiplier V hV F).val ^ 2 - 1 ∈ algebra (X := X) (H := H) := by
  have he := congrArg (fun T : multiplierAlgebra (X := X) (H := H) => T.val)
    (nonunitalIdentityExtension_square_defect (isometryCornerHom V hV) F)
  change (isometricMultiplier V hV F).val ^ 2 - 1 =
    V.val * (F.val ^ 2 - 1) * (star V).val at he
  rw [he]
  exact ((star V).property ⟨_, (V.property ⟨_, hFd⟩).1⟩).2

theorem rationalBoundaryUnitary_isometricMultiplier
    (V : multiplierAlgebra (X := X) (H := H)) (hV : star V * V = 1)
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F) :
    isometryExtensionUnitary V hV (rationalBoundaryUnitary F hF) =
      rationalBoundaryUnitary (isometricMultiplier V hV F)
        (isometricMultiplier_selfAdjoint V hV F hF) := by
  apply Subtype.ext
  rw [isometryExtensionUnitary_val]
  exact nonunital_rationalBoundaryUnitary (isometryCornerHom V hV) F hF

/-- Stabilizing a multiplier by an isometry does not change its actual Roe K₁ boundary. -/
theorem multiplierBoundaryClass_isometry
    (V : multiplierAlgebra (X := X) (H := H)) (hV : star V * V = 1)
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    multiplierBoundaryClass F hF hFd =
      multiplierBoundaryClass (isometricMultiplier V hV F)
        (isometricMultiplier_selfAdjoint V hV F hF)
        (isometricMultiplier_defect_mem V hV F hFd) := by
  let φ := (multiplierAlgebra (X := X) (H := H)).subtype
  have hφ : ∀ a b, b ∈ algebra (X := X) (H := H) →
      φ a * b ∈ algebra (X := X) (H := H) ∧
        b * φ a ∈ algebra (X := X) (H := H) := fun a b hb => a.property ⟨b, hb⟩
  have h := relativeClass_isometry (hS := algebra_isClosed)
    (algebra (X := X) (H := H)) φ continuous_subtype_val hφ V hV
    (rationalBoundaryUnitary F hF) (multiplierBoundaryUnitary_sub_one_mem F hF hFd)
  simp only [rationalBoundaryUnitary_isometricMultiplier V hV F hF] at h
  exact h

/-- Arbitrary multiplier unitaries preserve the boundary; no path is assumed. -/
theorem multiplierBoundaryClass_unitaryConjugation
    (u : unitary (multiplierAlgebra (X := X) (H := H)))
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) :
    multiplierBoundaryClass F hF hFd =
      multiplierBoundaryClass (conjugatedMultiplier u F)
        (conjugatedMultiplier_selfAdjoint u F hF)
        (conjugatedMultiplier_defect_mem u F hFd) := by
  have hV : star (u : multiplierAlgebra (X := X) (H := H)) * u = 1 :=
    Unitary.coe_star_mul_self u
  have hu : (u : multiplierAlgebra (X := X) (H := H)) *
      star (u : multiplierAlgebra (X := X) (H := H)) = 1 := by
    have h := Unitary.coe_mul_star_self u
    change (u : multiplierAlgebra (X := X) (H := H)) *
      star (u : multiplierAlgebra (X := X) (H := H)) = 1 at h
    exact h
  have he : isometricMultiplier (u : multiplierAlgebra (X := X) (H := H)) hV F =
      conjugatedMultiplier u F := by
    change 1 + (u : multiplierAlgebra (X := X) (H := H)) * (F - 1) *
      star (u : multiplierAlgebra (X := X) (H := H)) = _
    unfold conjugatedMultiplier
    rw [mul_sub, sub_mul, mul_one, hu]
    abel
  have h := multiplierBoundaryClass_isometry
    (u : multiplierAlgebra (X := X) (H := H)) hV F hF hFd
  simpa only [he] using h

end CoarseAssembly.DiscreteRoe

end

end OAI
