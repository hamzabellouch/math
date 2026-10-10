import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.CongruenceElementary
import OAI.Topology.CoarseAssembly.ConstructedConclusion

namespace OAI

/-! # The unconditional bounded-geometry counterexample

The geometric construction, analytic assembly, integral spectral certificate
and finite congruence generation are combined here.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

attribute [local instance] OAI.CoarseAssembly.unconditionalConclusionMetric

theorem provedKazhdanInput : PublishedKazhdanInput :=
  publishedKazhdanInput_of_elementaryReduction elementaryReduction_surjective

/-- The constructed ordinary coarse assembly map has an infinite-order
kernel class and fails injectivity both integrally and rationally. -/
theorem bounded_geometry_counterexample_unconditional :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ constructedCoarseAssembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective constructedCoarseAssembly ∧
        ¬ Function.Injective (constructedCoarseAssembly.toIntLinearMap.lTensor ℚ) :=
  bounded_geometry_counterexample_from_gap provedKazhdanInput

/-- The graph-family clauses of the main theorem, together with the full
coarse-assembly conclusion for its concrete separated union. -/
theorem bounded_geometry_graph_counterexample_unconditional :
    (∀ j, Finite (FiberVertex j) ∧
      (fiberedGraph elementaryMoves chosenHolonomyUnit j).Connected) ∧
    (∃ D : ℕ, ∀ j (x : FiberVertex j),
      Nat.card {y // (fiberedGraph elementaryMoves chosenHolonomyUnit j).Adj x y} ≤ D) ∧
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ constructedCoarseAssembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective constructedCoarseAssembly ∧
        ¬ Function.Injective (constructedCoarseAssembly.toIntLinearMap.lTensor ℚ) := by
  refine ⟨?_, ?_, bounded_geometry_counterexample_unconditional⟩
  · intro j
    exact ⟨inferInstance, fiberedGraph_connected elementaryMoves chosenHolonomyUnit j⟩
  · exact ⟨7 * (symmetricMoves elementaryMoves).card * 2 ^ 9,
      fun _ x => card_fibered_neighbors_le elementaryMoves chosenHolonomyUnit x⟩

end CoarseAssembly

end

end OAI
