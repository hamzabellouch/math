import OAI.Topology.CoarseAssembly.MultiplierBoundaryClass
import OAI.Topology.CoarseAssembly.CayleyNonunitalNaturality
import OAI.Topology.CoarseAssembly.RelativeNaturality
import OAI.Topology.CoarseAssembly.IsometricExtension
import OAI.Topology.CoarseAssembly.RoeTransfer

namespace OAI

/-! # The boundary representative respects spatial Roe maps

The target Fredholm operator is extended by the identity on the complement
of the spatial isometry. The conclusion is the actual K₁ map equality.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X Y H : Type*} [DecidableEq X] [DecidableEq Y]
  [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance spatialBoundaryScalarTower {Z : Type*} : IsScalarTower ℂ (Operator Z H) (Operator Z H) where
  smul_assoc c T S := by ext v; simp
local instance spatialBoundaryScalarComm {Z : Type*} : SMulCommClass ℂ (Operator Z H) (Operator Z H) where
  smul_comm c T S := by ext v; simp
local instance spatialBoundaryContinuousStar {Z : Type*} : ContinuousStar (Operator Z H) := ⟨operator_star_continuous⟩

theorem multiplierBoundaryUnitary_spatial
    (V : Module X H →ₗᵢ[ℂ] Module Y H)
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (G : multiplierAlgebra (X := Y) (H := H)) (hG : IsSelfAdjoint G)
    (hGF : G.val = isometricExtension V F.val) :
    (multiplierBoundaryUnitary G hG : Operator Y H) - 1 =
      operatorConjugation V ((multiplierBoundaryUnitary F hF : Operator X H) - 1) := by
  let φ : multiplierAlgebra (X := X) (H := H) →⋆ₙₐ[ℂ] Operator Y H :=
    (operatorConjugationHom V).comp
      (multiplierAlgebra (X := X) (H := H)).subtype.toNonUnitalStarAlgHom
  have he : Analytic.nonunitalIdentityExtension φ F = G.val := hGF.symm
  have h := Analytic.nonunital_rationalBoundaryUnitary φ F hF
  have hg := Analytic.map_rationalBoundaryUnitary
    (multiplierAlgebra (X := Y) (H := H)).subtype G hG
  have hg' : (multiplierBoundaryUnitary G hG : Operator Y H) =
      (Analytic.rationalBoundaryUnitary (Analytic.nonunitalIdentityExtension φ F)
        (Analytic.nonunitalIdentityExtension_selfAdjoint φ F hF) : Operator Y H) := by
    convert! hg using 2
    congr 1
  have hu : 1 + φ ((Analytic.rationalBoundaryUnitary F hF : multiplierAlgebra
      (X := X) (H := H)) - 1) = (multiplierBoundaryUnitary G hG : Operator Y H) :=
    h.trans hg'.symm
  have hu' := congrArg (fun T : Operator Y H => T - 1) hu.symm
  have hφ : φ ((Analytic.rationalBoundaryUnitary F hF :
      multiplierAlgebra (X := X) (H := H)) - 1) =
      operatorConjugation V ((multiplierBoundaryUnitary F hF : Operator X H) - 1) := rfl
  simpa only [add_sub_cancel_left, hφ] using hu'

theorem multiplierBoundaryClass_spatial
    (V : Module X H →ₗᵢ[ℂ] Module Y H) (hV : MapsToRoe V)
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (G : multiplierAlgebra (X := Y) (H := H)) (hG : IsSelfAdjoint G)
    (hGd : G.val ^ 2 - 1 ∈ algebra (X := Y) (H := H))
    (hGF : G.val = isometricExtension V F.val) :
    OperatorKTheory.map (conjugationHom V hV) (multiplierBoundaryClass F hF hFd) =
      multiplierBoundaryClass G hG hGd := by
  apply OperatorKTheory.map_relativeClass (hS := algebra_isClosed) (hT := algebra_isClosed)
  apply Subtype.ext
  exact (multiplierBoundaryUnitary_spatial V F hF G hG hGF).symm

end CoarseAssembly.DiscreteRoe

end

end OAI
