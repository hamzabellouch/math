import OAI.Topology.CoarseAssembly.WindingIndexEvaluation
import OAI.Topology.CoarseAssembly.PublishedInputReduction

namespace OAI

/-! # Reducing the circle input to one explicit index computation -/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

local instance circleReductionMetric : MetricSpace VertexUnion :=
  vertexUnionMetric elementaryMoves chosenHolonomyUnit

/-- The circle pairing and winding laws are now proved. Only a circle
class whose coordinate index is one is required from circle index theory. -/
theorem bounded_geometry_counterexample_of_circle_index_one
    (αcircle : LocallyFiniteK1 WindingCircle)
    (hcircle : compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle)) αcircle = 1)
    (hadd : CountableAdditivityInput CircleFamily) (hfill : CountableAdditivityInput FilledDisc)
    (index : PublishedBoundaryAssemblyInput) (hgap : PublishedKazhdanInput) :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ index.total.assembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective index.total.assembly ∧
        ¬ Function.Injective (index.total.assembly.toIntLinearMap.lTensor ℚ) :=
  bounded_geometry_counterexample_from_circle_index_gap
    (circleInputOfIndexOne αcircle hcircle) hadd hfill index hgap

end CoarseAssembly

end

end OAI
