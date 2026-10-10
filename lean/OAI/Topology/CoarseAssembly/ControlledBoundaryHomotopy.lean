import OAI.Topology.CoarseAssembly.ControlledBoundaryClass
import OAI.Topology.CoarseAssembly.CayleyContinuity
import OAI.Topology.CoarseAssembly.RelativeHomotopy

namespace OAI

/-! # Homotopies of controlled Fredholm operators give the same Roe class -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

open Analytic

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : IsScalarTower ℂ (Operator X H) (Operator X H) where
  smul_assoc c T S := by ext v; simp
local instance : SMulCommClass ℂ (Operator X H) (Operator X H) where
  smul_comm c T S := by ext v; simp
local instance : ContinuousStar (Operator X H) := ⟨operator_star_continuous⟩

variable (finiteBalls : ∀ x : X, ∀ r : ℝ, (Metric.closedBall x r).Finite)

theorem controlledBoundaryClass_homotopy
    (F : Interval → unitalStructureAlgebra (X := X) (H := H))
    (hF : ∀ t, IsSelfAdjoint (F t))
    (hdefect : ∀ t, (F t).val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hcont : Continuous F) :
    controlledBoundaryClass finiteBalls (F start) (hF start) (hdefect start) =
      controlledBoundaryClass finiteBalls (F finish) (hF finish) (hdefect finish) := by
  have hU : Continuous (fun t => (controlledBoundaryUnitary (F t) (hF t) : Operator X H)) := by
    convert! (show Continuous
      (fun T : unitalStructureAlgebra (X := X) (H := H) => T.val) from
        continuous_subtype_val).comp (continuous_rationalBoundaryUnitary F hF hcont)
  exact OperatorKTheory.relativeClass_homotopy (hS := algebra_isClosed)
    (algebra (X := X) (H := H)) (fun t => controlledBoundaryUnitary (F t) (hF t))
    (fun t => controlledBoundaryUnitary_sub_one_mem finiteBalls (F t) (hF t) (hdefect t)) hU

end CoarseAssembly.DiscreteRoe

end

end OAI
