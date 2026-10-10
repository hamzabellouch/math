import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.ConcreteIndexSquares
import OAI.Topology.CoarseAssembly.SeparatedIndexNaturality

namespace OAI

/-! # Discharging the published assembly interface

The three maps are the constructed analytic cycle index maps. Their two naturality squares follow from spatial inclusion, with
explicit reindexing of the manuscript's vertex sets.
-/

noncomputable section

namespace CoarseAssembly

open Analytic DiscreteRoe Rips Congruence

local instance assembledDiscEq (i : ℕ) : DecidableEq (Disc i) := Classical.decEq _
local instance assemblyBoundaryEq (i : ℕ) : DecidableEq (BoundaryComponent i) := Classical.decEq _
local instance assemblyFiberEq (i : ℕ) : DecidableEq (FiberVertex i) := Classical.decEq _
local instance assemblyBoundaryComponentMetric (i : ℕ) : MetricSpace (BoundaryComponent i) :=
  boundaryComponentMetric elementaryMoves chosenHolonomyUnit i
local instance assemblyBoundaryUnionMetric : MetricSpace (Sigma BoundaryComponent) := separatedMetric boundaryRoot
local instance assemblyBoundaryMetric : MetricSpace BoundaryVertex :=
  boundaryMetric elementaryMoves chosenHolonomyUnit
local instance assemblyFiberComponentMetric (i : ℕ) : MetricSpace (FiberVertex i) :=
  componentMetric elementaryMoves chosenHolonomyUnit i
local instance assemblyFiberUnionMetric : MetricSpace (Sigma FiberVertex) := separatedMetric fiberBoundaryBase
local instance assemblyTotalMetric : MetricSpace VertexUnion := vertexUnionMetric elementaryMoves chosenHolonomyUnit

theorem constructedBoundaryIndex_natural_base (n : ℕ) :
    (constructedBaseIndex.atScale n).comp (pushforward (boundaryBaseCoarsening.atScale n)) =
      (OperatorKTheory.map boundaryBaseRoeHom).comp (constructedBoundaryIndex.atScale n) := by
  apply DFunLike.ext
  intro a
  let b := pushforward (boundaryInverseCoarsening.atScale n) a
  let z := separatedRipsIndex boundaryRoot n (Nat.cast_nonneg n) b
  have h := DFunLike.congr_fun
    (separatedRipsIndex_inclusion boundaryRoot discBoundaryBase (Nat.cast_nonneg n)
      boundaryComponentToBase boundaryComponentToBase_nonexpanding (fun _ => rfl)
      boundaryBaseComponents_nonexpanding) b
  change separatedRipsIndex discBoundaryBase n (Nat.cast_nonneg n)
      (pushforward (boundaryBaseComponentsMap n) b) =
    OperatorKTheory.map boundaryBaseComponentsRoeHom z at h
  have hg := DFunLike.congr_fun (congrArg pushforward (boundaryBaseComponentsMap_eq n)) a
  have hp := DFunLike.congr_fun
    (pushforward_comp (boundaryInverseCoarsening.atScale n) (boundaryBaseComponentsMap n)) a
  have hg' := hp.symm.trans hg
  simp only [constructedBaseIndex, constructedBoundaryIndex, CompatibleIndexFamily.mapTarget,
    CompatibleIndexFamily.transport, separatedIndexFamily_atScale, AddMonoidHom.comp_apply]
  change OperatorKTheory.map baseReindexRoeHom
      (separatedRipsIndex discBoundaryBase n (Nat.cast_nonneg n)
        (pushforward (boundaryBaseCoarsening.atScale n) a)) =
    OperatorKTheory.map boundaryBaseRoeHom (OperatorKTheory.map boundaryReindexRoeHom z)
  have hk := DFunLike.congr_fun
    (congrArg OperatorKTheory.map boundaryBaseComponentsRoeHom_eq) z
  have hi := (congrArg (separatedRipsIndex discBoundaryBase n (Nat.cast_nonneg n)) hg').symm.trans h
  have hkl := DFunLike.congr_fun
    (OperatorKTheory.map_comp boundaryBaseComponentsRoeHom baseReindexRoeHom) z
  have hkr := DFunLike.congr_fun
    (OperatorKTheory.map_comp boundaryReindexRoeHom boundaryBaseRoeHom) z
  exact (congrArg (OperatorKTheory.map baseReindexRoeHom) hi).trans
    (hkl.symm.trans (hk.trans hkr))

theorem constructedBoundaryIndex_natural_total (n : ℕ) :
    (constructedTotalIndex.atScale n).comp (pushforward (boundaryTotalCoarsening.atScale n)) =
      (OperatorKTheory.map boundaryTotalRoeHom).comp (constructedBoundaryIndex.atScale n) := by
  apply DFunLike.ext
  intro a
  let b := pushforward (boundaryInverseCoarsening.atScale n) a
  let z := separatedRipsIndex boundaryRoot n (Nat.cast_nonneg n) b
  have h := DFunLike.congr_fun
    (separatedRipsIndex_inclusion boundaryRoot fiberBoundaryBase (Nat.cast_nonneg n)
      boundaryFiberEmbedding boundaryFiberComponent_nonexpanding (fun _ => rfl)
      boundaryFiberComponents_nonexpanding) b
  change separatedRipsIndex fiberBoundaryBase n (Nat.cast_nonneg n)
      (pushforward (boundaryFiberComponentsMap n) b) =
    OperatorKTheory.map boundaryFiberComponentsRoeHom z at h
  have hg := DFunLike.congr_fun (congrArg pushforward (boundaryFiberComponentsMap_eq n)) a
  have hp := DFunLike.congr_fun
    (pushforward_comp (boundaryInverseCoarsening.atScale n) (boundaryFiberComponentsMap n)) a
  have hq := DFunLike.congr_fun
    (pushforward_comp (boundaryTotalCoarsening.atScale n) (totalToFiberCoarsening.atScale n)) a
  have hg' := hp.symm.trans (hg.trans hq)
  simp only [constructedTotalIndex, constructedBoundaryIndex, CompatibleIndexFamily.transport,
    separatedIndexFamily_atScale, AddMonoidHom.comp_apply]
  change OperatorKTheory.map fiberReindexRoeHom
      (separatedRipsIndex fiberBoundaryBase n (Nat.cast_nonneg n)
        (pushforward (totalToFiberCoarsening.atScale n)
          (pushforward (boundaryTotalCoarsening.atScale n) a))) =
    OperatorKTheory.map boundaryTotalRoeHom (OperatorKTheory.map boundaryReindexRoeHom z)
  have hk := DFunLike.congr_fun
    (congrArg OperatorKTheory.map boundaryFiberComponentsRoeHom_eq) z
  have hi := (congrArg (separatedRipsIndex fiberBoundaryBase n (Nat.cast_nonneg n)) hg').symm.trans h
  have hkl := DFunLike.congr_fun
    (OperatorKTheory.map_comp boundaryFiberComponentsRoeHom fiberReindexRoeHom) z
  have hkr := DFunLike.congr_fun
    (OperatorKTheory.map_comp boundaryReindexRoeHom boundaryTotalRoeHom) z
  exact (congrArg (OperatorKTheory.map fiberReindexRoeHom) hi).trans
    (hkl.symm.trans (hk.trans hkr))

/-- The published interface is now supplied by the constructed analytic index. -/
def constructedBoundaryAssembly : PublishedBoundaryAssemblyInput where
  boundary := constructedBoundaryIndex
  base := constructedBaseIndex
  total := constructedTotalIndex
  natural_base := constructedBoundaryIndex_natural_base
  natural_total := constructedBoundaryIndex_natural_total

end CoarseAssembly

end

end OAI
