import OAI.Topology.CoarseAssembly.BoundaryConclusion
import OAI.Topology.CoarseAssembly.CompactHomotopy
import OAI.Topology.CoarseAssembly.PointCoefficient

namespace OAI

/-! # Discharging the compact-homotopy input

The conditional theorem is preserved. This specialization removes its
homotopy hypothesis using the proved Fredholm-cycle homotopy construction.
The odd coefficient group of a point is now proved by explicit Fredholm
normalization; the circle, additivity, index and Kazhdan inputs remain.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

theorem compactFillingInput (hpoint : Subsingleton (LocallyFiniteK1 Unit)) :
    PublishedCompactHomotopyInput where
  homotopy f g h := by
    obtain ⟨F⟩ := h
    exact compact_homotopy_invariance f g F
  point_odd_zero := hpoint

local instance inputReductionMetric : MetricSpace VertexUnion :=
  vertexUnionMetric elementaryMoves chosenHolonomyUnit

theorem bounded_geometry_counterexample_of_point_odd_zero (circle : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily)
    (hpoint : Subsingleton (LocallyFiniteK1 Unit)) (hfill : CountableAdditivityInput FilledDisc)
    (index : PublishedBoundaryAssemblyInput) (hgap : PublishedKazhdanInput) :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ index.total.assembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective index.total.assembly ∧
        ¬ Function.Injective (index.total.assembly.toIntLinearMap.lTensor ℚ) :=
  bounded_geometry_counterexample circle hadd (compactFillingInput hpoint) hfill index hgap

/-- The complete compact-filling input is now a theorem. -/
theorem provedCompactFillingInput : PublishedCompactHomotopyInput :=
  compactFillingInput point_odd_zero

/-- Main theorem after discharging compact homotopy invariance and the odd point coefficient. -/
theorem bounded_geometry_counterexample_from_circle_index_gap (circle : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) (hfill : CountableAdditivityInput FilledDisc)
    (index : PublishedBoundaryAssemblyInput) (hgap : PublishedKazhdanInput) :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ index.total.assembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective index.total.assembly ∧
        ¬ Function.Injective (index.total.assembly.toIntLinearMap.lTensor ℚ) :=
  bounded_geometry_counterexample circle hadd provedCompactFillingInput hfill index hgap

end CoarseAssembly

end

end OAI
