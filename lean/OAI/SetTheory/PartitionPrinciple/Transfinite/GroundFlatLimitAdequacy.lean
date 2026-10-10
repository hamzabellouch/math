import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFlatLimitConditions
import OAI.SetTheory.PartitionPrinciple.Transfinite.RefinementHistoryPrefixLevels

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementHistoryCandidate_cut (separation : SeparationSchema M.sets)
    {stages indexHistory rows T beta row A : ZFSet.{u}}
    (function : FunctionGraphOn stages indexHistory)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ indexHistory → RefinementIndexLevelCode I xi)
    (below : beta ⊆ stages)
    (hLevels : refinementHistoryAssignmentLevels stages indexHistory T ∈ M.sets)
    (hBeta : beta ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (candidate : ZFSet.pair row A ∈
      M.stageOneCandidateBound rows (refinementHistoryIndices stages indexHistory) T) :
    ZFSet.pair row (assignmentCut (refinementHistoryAssignmentLevels stages indexHistory T) beta A) ∈
      M.stageOneCandidateBound rows (refinementHistoryIndices beta indexHistory) T := by
  obtain ⟨hrow, hA, _, small⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  apply (M.pair_mem_stageOneCandidateBound _ _ _ _ _).2
  refine ⟨hrow, M.assignmentCut_mem separation hLevels hBeta hA, ?_,
    M.assignmentCut_small separation hLevels hBeta hA omega small⟩
  rw [refinementHistoryAssignmentCut_eq function literal below]
  exact fun _ member => (ZFSet.mem_sep.1 member).2

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {stages indexHistory history rows T : ZFSet.{u}}
variable (hStages : stages ∈ M.sets) (hIndexHistory : indexHistory ∈ M.sets) (hT : T ∈ M.sets)
variable (omega : ZFSet.omega ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (successors : ∀ beta ∈ stages, insert beta beta ∈ stages)
variable (function : FunctionGraphOn stages indexHistory)
variable (literal : ∀ xi I, ZFSet.pair xi I ∈ indexHistory → RefinementIndexLevelCode I xi)
variable (tests : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
variable (recursion : FlatOrdinalCarrierRecursion stages history
  (refinementHistoryAssignmentLevels stages indexHistory T)
  (fun beta row A => ZFSet.pair row A ∈
    M.stageOneCandidateBound rows (refinementHistoryIndices beta indexHistory) T) tests)
variable (locality : ∀ beta ∈ stages, ∀ row A,
  tests beta row (assignmentCut (refinementHistoryAssignmentLevels stages indexHistory T)
    (insert beta beta) A) ↔ tests beta row A)
include pairing unions powers separation hStages hIndexHistory hT omega ordinal successors function literal recursion locality

theorem flatLimitConditions_iff_all_tests (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.flatLimitConditions rows (refinementHistoryIndices stages indexHistory) T
      stages history (refinementHistoryAssignmentLevels stages indexHistory T) ↔
    ZFSet.pair row A ∈ M.stageOneCandidateBound rows (refinementHistoryIndices stages indexHistory) T ∧
      ∀ beta ∈ stages, tests beta row A := by
  have levels := M.refinementHistoryAssignmentLevels_mem pairing unions powers separation
    hStages hIndexHistory hT
  rw [M.mem_flatLimitConditions, flatLimitConditionCode_pair]
  apply and_congr_right
  intro candidate
  exact recursion.cuts_iff_tests ordinal locality successors row A (fun beta member =>
    M.refinementHistoryCandidate_cut separation function literal (ordinal.1 beta member)
      levels (M.transitive hStages member) omega candidate)

theorem flatLimitConditions_successor_coverage {row A : ZFSet.{u}}
    (member : ZFSet.pair row A ∈
      M.flatLimitConditions rows (refinementHistoryIndices stages indexHistory) T stages history
        (refinementHistoryAssignmentLevels stages indexHistory T)) :
    ∀ beta ∈ stages, ∃ Q Qnext,
      ZFSet.pair beta Q ∈ history ∧ ZFSet.pair (insert beta beta) Qnext ∈ history ∧
      ZFSet.pair row (assignmentCut (refinementHistoryAssignmentLevels stages indexHistory T) beta A) ∈ Q ∧
      ZFSet.pair row (assignmentCut (refinementHistoryAssignmentLevels stages indexHistory T)
        (insert beta beta) A) ∈ Qnext ∧ tests beta row A := by
  have allTests := ((M.flatLimitConditions_iff_all_tests pairing unions powers separation
    hStages hIndexHistory hT omega ordinal successors function literal tests recursion locality row A).1 member).2
  have cuts := (flatLimitConditionCode_pair _ _ _ _ _).1
    ((M.mem_flatLimitConditions _ _ _ _ _ _ _).1 member).2
  intro beta hbeta
  obtain ⟨Q, entry, lower⟩ := cuts beta hbeta
  obtain ⟨Qnext, next, upper⟩ := cuts (insert beta beta) (successors beta hbeta)
  exact ⟨Q, Qnext, entry, next, lower, upper, allTests beta hbeta⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
