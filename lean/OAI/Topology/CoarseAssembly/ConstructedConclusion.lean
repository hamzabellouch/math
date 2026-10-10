import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.ConstructedBoundaryAssembly
import OAI.Topology.CoarseAssembly.ExplicitBoundaryConclusion

namespace OAI

/-! # Counterexample for the constructed analytic coarse assembly map

Only the fixed-generator spectral-gap input remains in this theorem.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.constructedConclusionMetric

theorem bounded_geometry_counterexample_from_gap (hgap : PublishedKazhdanInput) :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ constructedCoarseAssembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective constructedCoarseAssembly ∧
        ¬ Function.Injective (constructedCoarseAssembly.toIntLinearMap.lTensor ℚ) :=
  bounded_geometry_counterexample_from_index_gap constructedBoundaryAssembly hgap

end CoarseAssembly

end

end OAI
