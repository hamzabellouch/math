import OAI.Topology.CoarseAssembly.BoundaryAssemblyMaps
import OAI.Topology.CoarseAssembly.BoundaryLoopMaps
import OAI.Topology.CoarseAssembly.ProperGeometry

namespace OAI

/-! # The boundary class in the reduced coarse assembly kernel

The filling and detector refer to the same explicitly parametrized family.
Those maps combine with the two stated published assembly naturality
equations.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

local instance boundaryConclusionMetric1 (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit j
local instance boundaryConclusionMetric2 (j : ℕ) : PseudoMetricSpace (BoundaryComponent j) :=
  (boundaryComponentMetric elementaryMoves chosenHolonomyUnit j).toPseudoMetricSpace
local instance boundaryConclusionMetric3 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
local instance boundaryConclusionMetric4 : PseudoMetricSpace BoundaryVertex :=
  (boundaryMetric elementaryMoves chosenHolonomyUnit).toPseudoMetricSpace
local instance boundaryConclusionMetric5 (j : ℕ) : MetricSpace (FiberVertex j) :=
  componentMetric elementaryMoves chosenHolonomyUnit j
local instance boundaryConclusionMetric6 : MetricSpace FiberedUnion := componentUnionMetric elementaryMoves chosenHolonomyUnit
local instance boundaryConclusionMetric7 : MetricSpace VertexUnion := vertexUnionMetric elementaryMoves chosenHolonomyUnit

def counterexampleClass (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) : KX1 VertexUnion :=
  boundaryTotalCoarsening.homologyMap (boundaryLoopClass input hadd)

theorem boundaryLoopClass_base_zero (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily)
    (homotopy : PublishedCompactHomotopyInput) (hfill : CountableAdditivityInput FilledDisc) :
    boundaryBaseCoarsening.homologyMap (boundaryLoopClass input hadd) = 0 := by
  change (embeddingCoarsening boundaryToBase
    (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)).homologyMap
    (classAt 1 1 (by norm_num) (boundaryLoopStage input hadd)) = 0
  rw [embedding_classAt, boundaryLoopStage_base_zero input hadd homotopy hfill, classAt_zero]

theorem counterexampleClass_image (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) :
    totalToFiberCoarsening.homologyMap (counterexampleClass input hadd) =
      concreteFiberClass input hadd := by
  change (embeddingCoarsening totalToFiber.toEmbedding
    (fun x y => (totalToFiber_dist x y).le)).homologyMap
    ((embeddingCoarsening boundaryToVertex
      (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)).homologyMap
      (classAt 1 1 (by norm_num) (boundaryLoopStage input hadd))) = _
  rw [embedding_classAt, embedding_classAt]
  have hs : pushforward (embeddingMap totalToFiber.toEmbedding
      (fun x y => (totalToFiber_dist x y).le) 1)
      (pushforward (embeddingMap boundaryToVertex
        (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit) 1)
        (boundaryLoopStage input hadd)) = realFiberStage input hadd 1 le_rfl := by
    have hp := congrArg pushforward boundaryFamily_toFiber
    have hv := DFunLike.congr_fun hp (boundaryCircleFamily input hadd)
    simpa only [pushforward_comp, AddMonoidHom.comp_apply, boundaryLoopStage,
      realFiberStage, fiberLoopsOne] using hv
  rw [hs]
  apply congrArg ((coarsening FiberedUnion).of 1)
  exact realFiberStage_cast input hadd 1 le_rfl 1 le_rfl (by norm_num)

theorem counterexampleClass_infinite_order (input : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily) (n : ℤ) (hn : n ≠ 0) :
    n • counterexampleClass input hadd ≠ 0 := by
  intro hz
  have h := congrArg totalToFiberCoarsening.homologyMap hz
  rw [map_zsmul, map_zero, counterexampleClass_image] at h
  exact concreteFiberClass_infinite_order input hadd n hn h

theorem counterexampleClass_index_zero (circle : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily)
    (homotopy : PublishedCompactHomotopyInput) (hfill : CountableAdditivityInput FilledDisc)
    (index : PublishedBoundaryAssemblyInput) (hgap : PublishedKazhdanInput) :
    index.total.assembly (counterexampleClass circle hadd) = 0 :=
  boundary_assembly_zero index hgap (boundaryLoopClass circle hadd)
    (boundaryLoopClass_base_zero circle hadd homotopy hfill)

/-- The manuscript's bounded-geometry rational counterexample, conditional
only on the precisely cited published analytic inputs. -/
theorem bounded_geometry_counterexample (circle : PublishedCircleInput)
    (hadd : CountableAdditivityInput CircleFamily)
    (homotopy : PublishedCompactHomotopyInput) (hfill : CountableAdditivityInput FilledDisc)
    (index : PublishedBoundaryAssemblyInput) (hgap : PublishedKazhdanInput) :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ index.total.assembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective index.total.assembly ∧
        ¬ Function.Injective (index.total.assembly.toIntLinearMap.lTensor ℚ) := by
  refine ⟨vertexUnion_proper elementaryMoves chosenHolonomyUnit,
    vertexUnion_uniform_balls elementaryMoves chosenHolonomyUnit,
    vertexUnion_separated elementaryMoves chosenHolonomyUnit,
    counterexampleClass circle hadd, counterexampleClass_infinite_order circle hadd,
    counterexampleClass_index_zero circle hadd homotopy hfill index hgap, ?_, ?_, ?_⟩
  · exact rationalization_ne_zero _ (counterexampleClass_infinite_order circle hadd)
  · exact (kernel_obstructs_injectivity index.total.assembly _
      (counterexampleClass_infinite_order circle hadd)
      (counterexampleClass_index_zero circle hadd homotopy hfill index hgap)).1
  · exact (kernel_obstructs_injectivity index.total.assembly _
      (counterexampleClass_infinite_order circle hadd)
      (counterexampleClass_index_zero circle hadd homotopy hfill index hgap)).2

end CoarseAssembly

end

end OAI
