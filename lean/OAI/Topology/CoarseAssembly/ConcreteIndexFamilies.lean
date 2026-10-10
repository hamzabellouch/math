import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.SeparatedCoarseAssembly
import OAI.Topology.CoarseAssembly.IndexFamilyTransport
import OAI.Topology.CoarseAssembly.ExplicitBoundaryRepresentative
import OAI.Topology.CoarseAssembly.RipsReindex

namespace OAI

/-! # The three constructed analytic index families used by the counterexample -/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance constructedDiscEq (i : ℕ) : DecidableEq (Disc i) := Classical.decEq _
local instance constructedBoundaryComponentEq (i : ℕ) : DecidableEq (BoundaryComponent i) := Classical.decEq _
attribute [local instance] OAI.CoarseAssembly.constructedFiberComponentEq

local instance constructedBoundaryComponentMetric (i : ℕ) : MetricSpace (BoundaryComponent i) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit i
local instance constructedBoundaryMetric : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
attribute [local instance] OAI.CoarseAssembly.constructedFiberComponentMetric

attribute [local instance] OAI.CoarseAssembly.constructedTotalMetric

private theorem boundaryReindex_isometry :
    letI := separatedMetric boundaryRoot
    Isometry boundaryReindex := by
  let := separatedMetric boundaryRoot
  exact Isometry.of_dist_eq (boundaryReindex_dist elementaryMoves chosenHolonomyUnit)

def boundaryInverseCoarsening : CoarseningMorphism (coarsening BoundaryVertex)
    (letI := separatedMetric boundaryRoot; coarsening (Sigma BoundaryComponent)) := by
  let := separatedMetric boundaryRoot
  exact embeddingCoarsening boundaryReindex.symm.toEmbedding
    (fun x y => ((equiv_inverse_isometry boundaryReindex boundaryReindex_isometry).dist_eq x y).le)

def constructedBoundaryIndex : CompatibleIndexFamily (coarsening BoundaryVertex) BoundaryRoe :=
  (separatedIndexFamily (Q := BoundaryComponent) boundaryRoot).transport boundaryInverseCoarsening boundaryReindexRoeHom

def separatedBaseEq : DecidableEq BaseUnion :=
  @instDecidableEqSigma ℕ Disc instDecidableEqNat constructedDiscEq

def baseReindexRoeHom :
    (letI := separatedBaseEq; algebra (X := BaseUnion) (H := AmpleSpace)) →⋆ₙₐ[ℂ] BaseRoe :=
  @inclusionHom BaseUnion BaseUnion AmpleSpace separatedBaseEq baseUnionDecidableEq
    _ _ _ _ _ (Function.Embedding.refl BaseUnion) (fun _ _ => le_rfl)

def constructedBaseIndex : CompatibleIndexFamily (coarsening BaseUnion) BaseRoe :=
  (separatedIndexFamily (Q := Disc) discBoundaryBase).mapTarget baseReindexRoeHom

end CoarseAssembly

end

end OAI
