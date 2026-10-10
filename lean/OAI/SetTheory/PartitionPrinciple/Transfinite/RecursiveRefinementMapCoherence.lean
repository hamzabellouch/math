import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRowCompleteProjection

namespace OAI

section

namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
open SetRealization
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (ordinal : ordinalSetProperty stages)
local notation "U" => M.refinementHistoryForcing rows T stages history
local notation "levels" => refinementDataHistoryLevels stages history T

theorem restrictionFunction_self_raw (x : SetMembers U) :
    SetMembers.raw (run.restrictionFunction ordinal ordinal (fun _ h => h) x) = SetMembers.raw x := by
  obtain ⟨row, _, A, _, code⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem x))
  have member := code ▸ SetMembers.raw_mem x
  have data := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
    ((M.mem_refinementHistoryForcing rows T stages history _).1 member).1).2.2.1
  rw [run.restrictionFunction_raw ordinal ordinal (fun _ h => h) x row A code,
    assignmentCut_full run.carriers.data.levels_function data, code]

theorem restrictionFunction_graph_self :
    (SetMembers.presentation U).graph
      (SetMembers.presentation (M.refinementHistoryForcing rows T stages (graphRestriction stages history)))
      (run.restrictionFunction ordinal ordinal (fun _ h => h)) = identityFunctionGraph U := by
  rw [run.restrictionFunction_graph, run.carriers.data.function.restriction_eq]
  apply rowAssignmentCutGraph_identity
  · intro p member
    obtain ⟨row, _, A, _, code⟩ := ZFSet.mem_prod.1 (M.refinementHistoryForcing_shape rows T stages history member)
    exact ⟨row, A, code⟩
  · intro row A member
    have data := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
      ((M.mem_refinementHistoryForcing rows T stages history _).1 member).1).2.2.1
    exact assignmentCut_full run.carriers.data.levels_function data

variable {alpha beta : ZFSet.{u}} (middleOrdinal : ordinalSetProperty alpha)
variable (lowerOrdinal : ordinalSetProperty beta) (subset : alpha ⊆ stages) (below : beta ⊆ alpha)
local notation "middleRun" => run.restrict middleOrdinal subset
local notation "V" => M.refinementHistoryForcing rows T alpha (graphRestriction alpha history)
local notation "W" => M.refinementHistoryForcing rows T beta (graphRestriction beta history)
local notation "nestedW" => M.refinementHistoryForcing rows T beta
  (graphRestriction beta (graphRestriction alpha history))
local notation "direct" => run.restrictionFunction ordinal lowerOrdinal (fun _ h => subset (below h))
local notation "first" => run.restrictionFunction ordinal middleOrdinal subset
local notation "second" => restrictionFunction (run.restrict middleOrdinal subset) middleOrdinal lowerOrdinal below

theorem restrictionFunction_comp_raw (x : SetMembers U) :
    SetMembers.raw (second (first x)) = SetMembers.raw (direct x) := by
  obtain ⟨row, _, A, _, code⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape rows T stages history (SetMembers.raw_mem x))
  have firstCode := run.restrictionFunction_raw ordinal middleOrdinal subset x row A code
  rw [(middleRun).restrictionFunction_raw middleOrdinal lowerOrdinal below (first x) row
      (assignmentCut levels alpha A) firstCode,
    run.restrictionFunction_raw ordinal lowerOrdinal (fun _ h => subset (below h)) x row A code,
    run.carriers.data.prefix_cut subset below, assignmentCut_nested below]

theorem restrictionFunction_graph_comp :
    relationCompose U V W
      ((SetMembers.presentation U).graph (SetMembers.presentation V) first)
      ((SetMembers.presentation V).graph (SetMembers.presentation nestedW) second) =
      (SetMembers.presentation U).graph (SetMembers.presentation W) direct := by
  rw [run.restrictionFunction_graph, (middleRun).restrictionFunction_graph,
    run.restrictionFunction_graph, graphRestriction_restrict below]
  apply rowAssignmentCutGraph_compose
  · intro row A member
    exact run.cut_mem_le ordinal middleOrdinal subset member
  · intro row A _
    rw [run.carriers.data.prefix_cut subset below, assignmentCut_nested below]

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

end

end OAI
