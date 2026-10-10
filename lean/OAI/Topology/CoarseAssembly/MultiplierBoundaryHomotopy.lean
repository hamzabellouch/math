import OAI.Topology.CoarseAssembly.MultiplierBoundaryClass
import OAI.Topology.CoarseAssembly.CayleyContinuity
import OAI.Topology.CoarseAssembly.RelativeHomotopy

namespace OAI

/-! # Norm homotopy invariance of the Roe multiplier boundary class -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance multiplierHomotopyScalarTower : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance multiplierHomotopyScalarComm : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp
local instance multiplierHomotopyContinuousStar : ContinuousStar (Operator X H) := ⟨operator_star_continuous⟩

theorem multiplierBoundaryClass_homotopy
    (F : Interval → multiplierAlgebra (X := X) (H := H))
    (hF : ∀ t, IsSelfAdjoint (F t))
    (hdefect : ∀ t, (F t).val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hcont : Continuous F) :
    multiplierBoundaryClass (F start) (hF start) (hdefect start) =
      multiplierBoundaryClass (F finish) (hF finish) (hdefect finish) := by
  have hU : Continuous (fun t => (multiplierBoundaryUnitary (F t) (hF t) : Operator X H)) := by
    convert! (show Continuous
      (fun T : multiplierAlgebra (X := X) (H := H) => T.val) from
        continuous_subtype_val).comp (continuous_rationalBoundaryUnitary F hF hcont)
  exact OperatorKTheory.relativeClass_homotopy (hS := algebra_isClosed)
    (algebra (X := X) (H := H)) (fun t => multiplierBoundaryUnitary (F t) (hF t))
    (fun t => multiplierBoundaryUnitary_sub_one_mem (F t) (hF t) (hdefect t)) hU

theorem multiplierBoundaryClass_eq_zero
    (F : multiplierAlgebra (X := X) (H := H)) (hF : IsSelfAdjoint F)
    (hdefect : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H)) (hsq : F * F = 1) :
    multiplierBoundaryClass F hF hdefect = 0 := by
  apply OperatorKTheory.relativeClass_eq_zero (hS := algebra_isClosed)
  have hu := Analytic.rationalBoundaryUnitary_eq_one F hF hsq
  apply Subtype.ext
  change ((Analytic.rationalBoundaryUnitary F hF : multiplierAlgebra (X := X) (H := H)) : Operator X H) = 1
  rw [hu]
  rfl

end CoarseAssembly.DiscreteRoe

end

end OAI
