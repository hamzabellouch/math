import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.BoundaryGeometry
import OAI.Topology.CoarseAssembly.KazhdanInput
import OAI.Topology.CoarseAssembly.BoundaryIndex

namespace OAI

/-! # The actual boundary assembly diagram

All three Roe maps below are constructed spatial homomorphisms on the
ordinary reduced locally compact Roe algebras. The transfer factorization
is proved before the two published assembly naturality equations are used.
-/

noncomputable section

namespace CoarseAssembly

open Congruence Analytic DiscreteRoe

attribute [local instance] OAI.CoarseAssembly.boundaryAssemblyMetric1

local instance boundaryAssemblyMetric2 : MetricSpace BoundaryVertex := boundaryMetric elementaryMoves chosenHolonomyUnit
local instance boundaryAssemblyMetric3 : PseudoMetricSpace BoundaryVertex :=
  (boundaryMetric elementaryMoves chosenHolonomyUnit).toPseudoMetricSpace

def BoundaryRoe : Type := algebra (X := BoundaryVertex) (H := AmpleSpace)
def BaseRoe : Type := algebra (X := BaseUnion) (H := AmpleSpace)
instance : NonUnitalCStarAlgebra BoundaryRoe :=
  inferInstanceAs (NonUnitalCStarAlgebra (algebra (X := BoundaryVertex) (H := AmpleSpace)))
instance : NonUnitalCStarAlgebra BaseRoe :=
  inferInstanceAs (NonUnitalCStarAlgebra (algebra (X := BaseUnion) (H := AmpleSpace)))
def boundaryBaseCoarsening : CoarseningMorphism (Rips.coarsening BoundaryVertex)
    (Rips.coarsening BaseUnion) :=
  Rips.embeddingCoarsening boundaryToBase
    (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)

def boundaryTotalCoarsening : CoarseningMorphism (Rips.coarsening BoundaryVertex)
    (Rips.coarsening VertexUnion) :=
  Rips.embeddingCoarsening boundaryToVertex
    (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)

def boundaryBaseRoeHom : BoundaryRoe →⋆ₙₐ[ℂ] BaseRoe :=
  inclusionHom (X := BoundaryVertex) (Y := BaseUnion) (H := AmpleSpace)
    boundaryToBase (boundaryToBase_nonexpanding elementaryMoves chosenHolonomyUnit)

def boundaryTotalRoeHom : BoundaryRoe →⋆ₙₐ[ℂ] TotalRoe :=
  inclusionHom (X := BoundaryVertex) (Y := VertexUnion) (H := AmpleSpace)
    boundaryToVertex (boundaryToVertex_nonexpanding elementaryMoves chosenHolonomyUnit)

def transferRoeHom (hgap : PublishedKazhdanInput) : BaseRoe →⋆ₙₐ[ℂ] TotalRoe :=
  conjugationHom (D := BaseUnion) (X := VertexUnion) (H := AmpleSpace)
    (fiberEmbedding (H := AmpleSpace) BaseFiber) (roe_transfer_of_published_gap hgap)

theorem transferRoeHom_boundary (hgap : PublishedKazhdanInput) :
    (transferRoeHom hgap).comp boundaryBaseRoeHom = boundaryTotalRoeHom := by
  apply DFunLike.ext
  intro T
  apply Subtype.ext
  change operatorConjugation (fiberEmbedding (H := AmpleSpace) BaseFiber)
      (operatorConjugation (boundaryBaseIsometry (H := AmpleSpace)) T.1) =
    operatorConjugation (boundaryVertexIsometry (H := AmpleSpace)) T.1
  exact boundary_operator_factorization (H := AmpleSpace) T.1

theorem transferK1_boundary (hgap : PublishedKazhdanInput) :
    (OperatorKTheory.map (transferRoeHom hgap)).comp (OperatorKTheory.map boundaryBaseRoeHom) =
      OperatorKTheory.map boundaryTotalRoeHom := by
  exact (OperatorKTheory.map_comp boundaryBaseRoeHom (transferRoeHom hgap)).symm.trans
    (congrArg OperatorKTheory.map (transferRoeHom_boundary hgap))

/-- The exact published index/naturality specializations used here:
Willett--Yu, *Higher Index Theory* (2020), §§5.1, 6.7, 7.1--7.2,
with errata 30--31. The objects and both geometric/Roe maps are fixed above.
There is no transfer-naturality premise. -/
structure PublishedBoundaryAssemblyInput where
  boundary : CompatibleIndexFamily (Rips.coarsening BoundaryVertex) BoundaryRoe
  base : CompatibleIndexFamily (Rips.coarsening BaseUnion) BaseRoe
  total : CompatibleIndexFamily (Rips.coarsening VertexUnion) TotalRoe
  natural_base : ∀ r, (base.atScale r).comp (pushforward (boundaryBaseCoarsening.atScale r)) =
    (OperatorKTheory.map boundaryBaseRoeHom).comp (boundary.atScale r)
  natural_total : ∀ r, (total.atScale r).comp (pushforward (boundaryTotalCoarsening.atScale r)) =
    (OperatorKTheory.map boundaryTotalRoeHom).comp (boundary.atScale r)

/-- Vanishing in the base annihilates the included boundary index by the
proved spatial transfer. Filling is a geometric premise, not a published input. -/
theorem boundary_assembly_zero (input : PublishedBoundaryAssemblyInput)
    (hgap : PublishedKazhdanInput) (β : Rips.KX1 BoundaryVertex)
    (hfilled : boundaryBaseCoarsening.homologyMap β = 0) :
    input.total.assembly (boundaryTotalCoarsening.homologyMap β) = 0 := by
  exact boundary_index_zero boundaryBaseCoarsening.homologyMap
    boundaryTotalCoarsening.homologyMap input.boundary.assembly input.base.assembly
    input.total.assembly (OperatorKTheory.map boundaryBaseRoeHom)
    (OperatorKTheory.map boundaryTotalRoeHom) (OperatorKTheory.map (transferRoeHom hgap))
    (input.boundary.assembly_natural input.base boundaryBaseCoarsening
      boundaryBaseRoeHom input.natural_base)
    (input.boundary.assembly_natural input.total boundaryTotalCoarsening
      boundaryTotalRoeHom input.natural_total)
    (transferK1_boundary hgap) β hfilled

end CoarseAssembly

end

end OAI
