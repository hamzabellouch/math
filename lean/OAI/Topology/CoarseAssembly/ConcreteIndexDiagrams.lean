import OAI.Topology.CoarseAssembly.ConcreteIndexFamilies
import OAI.Topology.CoarseAssembly.InclusionFunctoriality
import OAI.Topology.CoarseAssembly.ComponentInclusion

namespace OAI

/-! # The exact geometric and Roe squares for the two boundary inclusions -/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance concreteDiscEq (i : ℕ) : DecidableEq (Disc i) := Classical.decEq _
local instance concreteDiagramBoundaryEq (i : ℕ) : DecidableEq (BoundaryComponent i) := Classical.decEq _
local instance concreteDiagramFiberEq (i : ℕ) : DecidableEq (FiberVertex i) := Classical.decEq _
local instance concreteDiagramBoundaryComponentMetric (i : ℕ) : MetricSpace (BoundaryComponent i) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit i
local instance concreteDiagramBoundaryMetric : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
local instance concreteDiagramFiberComponentMetric (i : ℕ) : MetricSpace (FiberVertex i) :=
  componentMetric elementaryMoves chosenHolonomyUnit i
local instance concreteDiagramTotalMetric : MetricSpace VertexUnion :=
  vertexUnionMetric elementaryMoves chosenHolonomyUnit

local instance diagramBoundaryUnionMetric : MetricSpace (Sigma BoundaryComponent) := separatedMetric boundaryRoot
local instance diagramFiberUnionMetric : MetricSpace (Sigma FiberVertex) := separatedMetric fiberBoundaryBase
local instance diagramBoundaryRoeAdd : AddCommMonoid (algebra (X := Sigma BoundaryComponent) (H := AmpleSpace)) := inferInstance
local instance diagramFiberRoeAdd : AddCommMonoid (algebra (X := Sigma FiberVertex) (H := AmpleSpace)) := inferInstance
local instance diagramBaseRoeAdd : AddCommMonoid (letI := separatedBaseEq; algebra (X := BaseUnion) (H := AmpleSpace)) := by
  letI := separatedBaseEq
  infer_instance

theorem boundaryBaseComponents_nonexpanding :
    letI := separatedMetric boundaryRoot
    ∀ x y, dist (componentEmbedding boundaryComponentToBase x)
      (componentEmbedding boundaryComponentToBase y) ≤ dist x y :=
  componentEmbedding_nonexpanding boundaryRoot discBoundaryBase boundaryComponentToBase
    boundaryComponentToBase_nonexpanding (fun _ => rfl)

theorem boundaryFiberComponent_nonexpanding (i : ℕ) (x y : BoundaryComponent i) :
    dist (boundaryFiberEmbedding i x) (boundaryFiberEmbedding i y) ≤ dist x y := le_rfl

theorem boundaryFiberComponents_nonexpanding :
    letI := separatedMetric boundaryRoot
    letI := separatedMetric fiberBoundaryBase
    ∀ x y, dist (componentEmbedding boundaryFiberEmbedding x)
      (componentEmbedding boundaryFiberEmbedding y) ≤ dist x y :=
  componentEmbedding_nonexpanding boundaryRoot fiberBoundaryBase boundaryFiberEmbedding
    boundaryFiberComponent_nonexpanding (fun _ => rfl)

def boundaryBaseComponentsRoeHom :
    (letI := separatedMetric boundaryRoot;
      algebra (X := Sigma BoundaryComponent) (H := AmpleSpace)) →⋆ₙₐ[ℂ]
    (letI := separatedBaseEq; algebra (X := BaseUnion) (H := AmpleSpace)) := by
  let := separatedMetric boundaryRoot
  exact @inclusionHom (Sigma BoundaryComponent) BaseUnion AmpleSpace _ separatedBaseEq
    _ _ _ _ _ (componentEmbedding boundaryComponentToBase) boundaryBaseComponents_nonexpanding

def boundaryFiberComponentsRoeHom :
    (letI := separatedMetric boundaryRoot;
      algebra (X := Sigma BoundaryComponent) (H := AmpleSpace)) →⋆ₙₐ[ℂ]
    (letI := separatedMetric fiberBoundaryBase;
      algebra (X := Sigma FiberVertex) (H := AmpleSpace)) := by
  let := separatedMetric boundaryRoot
  let := separatedMetric fiberBoundaryBase
  exact inclusionHom (X := Sigma BoundaryComponent) (Y := Sigma FiberVertex) (H := AmpleSpace)
    (componentEmbedding boundaryFiberEmbedding) boundaryFiberComponents_nonexpanding

theorem boundaryBaseComponentsRoeHom_eq :
    baseReindexRoeHom.comp boundaryBaseComponentsRoeHom =
      boundaryBaseRoeHom.comp boundaryReindexRoeHom := by
  let := separatedMetric boundaryRoot
  have hf := @inclusionHom_comp (Sigma BoundaryComponent) BaseUnion BaseUnion AmpleSpace
    _ separatedBaseEq baseUnionDecidableEq _ _ _ _ _ _
    (componentEmbedding boundaryComponentToBase) (Function.Embedding.refl BaseUnion)
    boundaryBaseComponents_nonexpanding (fun _ _ => le_rfl)
  have hb := inclusionHom_comp (X := Sigma BoundaryComponent) (Y := BoundaryVertex) (Z := BaseUnion)
    (H := AmpleSpace) boundaryReindex.toEmbedding boundaryToBase
    (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)
    (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)
  exact hf.trans hb.symm

theorem boundaryFiberComponentsRoeHom_eq :
    fiberReindexRoeHom.comp boundaryFiberComponentsRoeHom =
      boundaryTotalRoeHom.comp boundaryReindexRoeHom := by
  let := separatedMetric boundaryRoot
  let := separatedMetric fiberBoundaryBase
  have hf := inclusionHom_comp (X := Sigma BoundaryComponent) (Y := Sigma FiberVertex)
    (Z := VertexUnion) (H := AmpleSpace)
    (componentEmbedding boundaryFiberEmbedding) totalToFiber.symm.toEmbedding
    boundaryFiberComponents_nonexpanding
    (fun x y => ((equiv_inverse_isometry totalToFiber
      (Isometry.of_dist_eq totalToFiber_dist)).dist_eq x y).le)
  have hb := inclusionHom_comp (X := Sigma BoundaryComponent) (Y := BoundaryVertex)
    (Z := VertexUnion) (H := AmpleSpace) boundaryReindex.toEmbedding boundaryToVertex
    (fun x y => (boundaryReindex_dist elementaryMoves chosenHolonomyUnit x y).le)
    (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)
  exact hf.trans hb.symm

end CoarseAssembly

end

end OAI
