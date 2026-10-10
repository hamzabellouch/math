import OAI.Topology.CoarseAssembly.CoefficientIsometry
import OAI.Topology.CoarseAssembly.AmpleRipsFamily
import OAI.Topology.CoarseAssembly.RipsInclusionNaturality

namespace OAI

/-! # Ample coefficient transport commutes with vertex inclusion -/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

variable {X Y E H : Type*} [DecidableEq X] [DecidableEq Y]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [DecidableEq X] [DecidableEq Y] in
theorem coefficientIsometry_inclusion (V : E →ₗᵢ[ℂ] H) (e : X ↪ Y) :
    (coefficientIsometry (X := Y) V).comp (inclusionIsometry (H := E) e) =
      (inclusionIsometry (H := H) e).comp (coefficientIsometry (X := X) V) := by
  apply DFunLike.ext
  intro v
  apply lp.ext
  funext y
  change V (inclusionVector e v y) = inclusionVector e (coefficientIsometry V v) y
  by_cases hy : y ∈ Set.range e
  · obtain ⟨x, rfl⟩ := hy
    rw [inclusionVector_apply, inclusionVector_apply, coefficientIsometry_apply]
  · rw [inclusionVector_zero e _ _ hy, inclusionVector_zero e _ _ hy, map_zero]

end CoarseAssembly.DiscreteRoe

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem ampleRipsOperator_inclusion (r : ℝ) (e : X ↪ Y)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (c : OddCycle C(Point X r, ℂ)) (hπ : c.representation 1 = 1) :
    ampleRipsOperator r (includedCycle r e he c) (includedCycle_unital r e he c hπ) =
      isometricExtension (inclusionIsometry e) (ampleRipsOperator r c hπ) := by
  let V := ampleIsometry c.space
  change isometricExtension (coefficientIsometry (X := Y) V)
      (ripsSpatialOperator r (includedCycle r e he c) (includedCycle_unital r e he c hπ)) =
    isometricExtension (inclusionIsometry e)
      (isometricExtension (coefficientIsometry (X := X) V) (ripsSpatialOperator r c hπ))
  have h := ripsSpatialOperator_inclusion r e he c hπ
  rw [h]
  simp only [isometricExtension_comp, coefficientIsometry_inclusion]

end CoarseAssembly.Rips

end

end OAI
