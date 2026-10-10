import OAI.Topology.CoarseAssembly.ConcreteIndexDiagrams

namespace OAI

/-! # Exact Rips-map squares for the constructed index families -/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance squareDiscEq (i : ℕ) : DecidableEq (Disc i) := Classical.decEq _
local instance indexSquareBoundaryEq (i : ℕ) : DecidableEq (BoundaryComponent i) := Classical.decEq _
local instance indexSquareFiberEq (i : ℕ) : DecidableEq (FiberVertex i) := Classical.decEq _
local instance indexSquareBoundaryComponentMetric (i : ℕ) : MetricSpace (BoundaryComponent i) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit i
local instance indexSquareBoundaryUnionMetric : MetricSpace (Sigma BoundaryComponent) := separatedMetric boundaryRoot
local instance indexSquareBoundaryMetric : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
local instance indexSquareFiberComponentMetric (i : ℕ) : MetricSpace (FiberVertex i) :=
  componentMetric elementaryMoves chosenHolonomyUnit i
local instance indexSquareFiberUnionMetric : MetricSpace (Sigma FiberVertex) := separatedMetric fiberBoundaryBase
local instance indexSquareTotalMetric : MetricSpace VertexUnion := vertexUnionMetric elementaryMoves chosenHolonomyUnit

def boundaryBaseComponentsMap (r : ℝ) : CocompactMap (Point (Sigma BoundaryComponent) r) (Point BaseUnion r) :=
  embeddingMap (componentEmbedding boundaryComponentToBase) boundaryBaseComponents_nonexpanding r

def boundaryFiberComponentsMap (r : ℝ) :
    CocompactMap (Point (Sigma BoundaryComponent) r) (Point (Sigma FiberVertex) r) :=
  embeddingMap (componentEmbedding boundaryFiberEmbedding) boundaryFiberComponents_nonexpanding r

theorem boundaryBaseComponentsMap_eq (n : ℕ) :
    (boundaryBaseComponentsMap n).comp (boundaryInverseCoarsening.atScale n) =
      boundaryBaseCoarsening.atScale n := by
  change (embeddingMap _ _ _).comp (embeddingMap _ _ _) = embeddingMap _ _ _
  rw [embeddingMap_comp]
  rfl

theorem boundaryFiberComponentsMap_eq (n : ℕ) :
    (boundaryFiberComponentsMap n).comp (boundaryInverseCoarsening.atScale n) =
      (totalToFiberCoarsening.atScale n).comp (boundaryTotalCoarsening.atScale n) := by
  change (embeddingMap _ _ _).comp (embeddingMap _ _ _) =
    (embeddingMap _ _ _).comp (embeddingMap _ _ _)
  rw [embeddingMap_comp, embeddingMap_comp]
  rfl

end CoarseAssembly

end

end OAI
