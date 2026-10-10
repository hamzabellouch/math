import OAI.Topology.CoarseAssembly.RelativeNearby
import OAI.Topology.CoarseAssembly.CayleyNormControl
import OAI.Topology.CoarseAssembly.MultiplierBoundaryClass

namespace OAI

/-! # Norm-local constancy of the actual Roe boundary class -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X H : Type*} [DecidableEq X] [PseudoMetricSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem multiplierBoundaryClass_eq_of_nearby
    (F G : multiplierAlgebra (X := X) (H := H))
    (hF : IsSelfAdjoint F) (hG : IsSelfAdjoint G)
    (hFd : F.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hGd : G.val ^ 2 - 1 ∈ algebra (X := X) (H := H))
    (hnear : ‖G - F‖ < (1 / 4 : ℝ)) :
    multiplierBoundaryClass F hF hFd = multiplierBoundaryClass G hG hGd := by
  apply OperatorKTheory.relativeClass_eq_of_nearby (hS := algebra_isClosed)
  have hb := Analytic.rationalBoundaryUnitary_sub_norm_le G F hG hF
  change ‖(Analytic.rationalBoundaryUnitary G hG : multiplierAlgebra (X := X) (H := H)) -
    Analytic.rationalBoundaryUnitary F hF‖ < 1
  exact hb.trans_lt (by linarith)

end CoarseAssembly.DiscreteRoe

end

end OAI
