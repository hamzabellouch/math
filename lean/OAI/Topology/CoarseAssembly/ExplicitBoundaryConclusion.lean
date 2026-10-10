import OAI.Topology.CoarseAssembly.ExplicitFamilyFilling
import OAI.Topology.CoarseAssembly.ExplicitPersistence
import OAI.Topology.CoarseAssembly.BoundaryConclusion

namespace OAI

/-! # The counterexample with circle, filling and additivity inputs discharged -/

noncomputable section

namespace CoarseAssembly

open Congruence Rips Analytic

local instance explicitBoundaryMetric1 (j : ℕ) : MetricSpace (BoundaryComponent j) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit j
local instance explicitBoundaryMetric2 (j : ℕ) : PseudoMetricSpace (BoundaryComponent j) :=
  (boundaryComponentMetric elementaryMoves chosenHolonomyUnit j).toPseudoMetricSpace
local instance explicitBoundaryMetric3 : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
local instance explicitBoundaryMetric4 : PseudoMetricSpace BoundaryVertex :=
  (boundaryMetric elementaryMoves chosenHolonomyUnit).toPseudoMetricSpace
local instance explicitBoundaryMetric5 (j : ℕ) : MetricSpace (FiberVertex j) :=
  componentMetric elementaryMoves chosenHolonomyUnit j
local instance explicitBoundaryMetric6 : MetricSpace FiberedUnion :=
  componentUnionMetric elementaryMoves chosenHolonomyUnit
local instance explicitBoundaryMetric7 : MetricSpace VertexUnion :=
  vertexUnionMetric elementaryMoves chosenHolonomyUnit

def explicitBoundaryStage : LocallyFiniteK1 (Point BoundaryVertex 1) :=
  pushforward (boundaryFamilyMap elementaryMoves chosenHolonomyUnit 1 boundaryLoops)
    explicitCircleFamily

def explicitBoundaryClass : KX1 BoundaryVertex :=
  classAt 1 1 (by norm_num) explicitBoundaryStage

def explicitCounterexampleClass : KX1 VertexUnion :=
  boundaryTotalCoarsening.homologyMap explicitBoundaryClass

def explicitRealFiberStage (r : ℝ) (hr : 1 ≤ r) :
    LocallyFiniteK1 (Point FiberedUnion r) :=
  pushforward (ripsFamilyMap fiberBoundaryBase r (realFiberLoops r hr)) explicitCircleFamily

theorem explicitRealFiberStage_cast (n : ℕ) (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) (h : r = (n : ℝ)) :
    (h ▸ explicitRealFiberStage r hr) = explicitFiberStage n hn := by
  subst r
  rfl

theorem explicitBoundaryStage_base_zero :
    pushforward (embeddingMap boundaryToBase
      (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit) 1)
      explicitBoundaryStage = 0 := by
  change pushforward _ (pushforward _ explicitCircleFamily) = 0
  rw [← AddMonoidHom.comp_apply, ← pushforward_comp, boundaryFamily_toBase]
  exact explicitBaseBoundaryFamily_zero discBoundaryBase concreteBaseWalk

theorem explicitBoundaryClass_base_zero :
    boundaryBaseCoarsening.homologyMap explicitBoundaryClass = 0 := by
  change (embeddingCoarsening boundaryToBase
    (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)).homologyMap
    (classAt 1 1 (by norm_num) explicitBoundaryStage) = 0
  rw [embedding_classAt, explicitBoundaryStage_base_zero, classAt_zero]

theorem explicitCounterexampleClass_image :
    totalToFiberCoarsening.homologyMap explicitCounterexampleClass = explicitFiberClass := by
  change (embeddingCoarsening totalToFiber.toEmbedding
    (fun x y => (totalToFiber_dist x y).le)).homologyMap
    ((embeddingCoarsening boundaryToVertex
      (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)).homologyMap
      (classAt 1 1 (by norm_num) explicitBoundaryStage)) = _
  rw [embedding_classAt, embedding_classAt]
  have hs : pushforward (embeddingMap totalToFiber.toEmbedding
      (fun x y => (totalToFiber_dist x y).le) 1)
      (pushforward (embeddingMap boundaryToVertex
        (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit) 1)
        explicitBoundaryStage) = explicitRealFiberStage 1 le_rfl := by
    have hp := congrArg pushforward boundaryFamily_toFiber
    have hv := DFunLike.congr_fun hp explicitCircleFamily
    simpa only [pushforward_comp, AddMonoidHom.comp_apply, explicitBoundaryStage,
      explicitRealFiberStage, fiberLoopsOne] using hv
  rw [hs]
  apply congrArg ((coarsening FiberedUnion).of 1)
  exact explicitRealFiberStage_cast 1 le_rfl 1 le_rfl (by norm_num)

theorem explicitCounterexampleClass_infinite_order (n : ℤ) (hn : n ≠ 0) :
    n • explicitCounterexampleClass ≠ 0 := by
  intro hz
  have h := congrArg totalToFiberCoarsening.homologyMap hz
  rw [map_zsmul, map_zero, explicitCounterexampleClass_image] at h
  exact explicitFiberClass_infinite_order n hn h

theorem explicitCounterexampleClass_index_zero (index : PublishedBoundaryAssemblyInput)
    (hgap : PublishedKazhdanInput) : index.total.assembly explicitCounterexampleClass = 0 :=
  boundary_assembly_zero index hgap explicitBoundaryClass explicitBoundaryClass_base_zero

/-- The full geometric conclusion, with only canonical assembly and the fixed-generator
published Kazhdan gap remaining. The particular countable class and its filling are proved. -/
theorem bounded_geometry_counterexample_from_index_gap
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
    explicitCounterexampleClass, explicitCounterexampleClass_infinite_order,
    explicitCounterexampleClass_index_zero index hgap, ?_, ?_, ?_⟩
  · exact rationalization_ne_zero _ explicitCounterexampleClass_infinite_order
  · exact (kernel_obstructs_injectivity index.total.assembly _
      explicitCounterexampleClass_infinite_order
      (explicitCounterexampleClass_index_zero index hgap)).1
  · exact (kernel_obstructs_injectivity index.total.assembly _
      explicitCounterexampleClass_infinite_order
      (explicitCounterexampleClass_index_zero index hgap)).2

end CoarseAssembly

end

end OAI
