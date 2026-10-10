import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundFlatLimitAdequacy
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralHistoryTestUnions

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {stages history T : ZFSet.{u}}
variable (function : FunctionGraphOn stages history)
variable (decoded : ∀ beta data, ZFSet.pair beta data ∈ history →
  ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d)
variable (literal : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history → RefinementIndexLevelCode (d 0) beta)
variable (commonT : ∀ beta (d : Fin 15 → ZFSet.{u}),
  ZFSet.pair beta (refinementFormulaDataCode d) ∈ history → d 6 = T)
include function decoded literal commonT

theorem forcingHistoryRawTests_successor_cut (beta row A : ZFSet.{u}) :
    forcingHistoryRawTests M history
      (refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T)
      beta row (assignmentCut
        (refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T)
        (insert beta beta) A) ↔
    forcingHistoryRawTests M history
      (refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T)
      beta row A := by
  apply forcingHistoryRawTests_cut_iff M _ _ _ _ _ _ (fun _ member => ZFSet.mem_insert_of_mem beta member)
  intro d entry t ht u hu w hw
  refine ⟨beta, ZFSet.mem_insert beta beta, ?_⟩
  have indexFunction := refinementDataHistoryField_function function decoded 0
  have indexLiteral := refinementDataHistoryField_index_levels (stages := stages) literal
  apply (refinementHistoryAssignmentLevels_entry indexFunction indexLiteral T t u w beta).2
  rw [commonT beta d entry] at hu hw
  exact ⟨d 0, (refinementDataHistoryField_entry function d entry 0 _).2 rfl, ht, hu, hw⟩

namespace TransitiveGround
variable {rows : ZFSet.{u}}
variable (successors : ∀ beta ∈ stages, insert beta beta ∈ stages)
variable (recursion : FlatOrdinalCarrierRecursion stages (refinementDataHistoryField stages history 7)
  (refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T)
  (fun beta row A => ZFSet.pair row A ∈
    M.stageOneCandidateBound rows
      (refinementHistoryIndices beta (refinementDataHistoryField stages history 0)) T)
  (forcingHistoryRawTests M history
    (refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T)))
include successors recursion

theorem forcingHistoryConditions_eq_flatLimit :
    M.forcingHistoryConditions rows
      (refinementHistoryIndices stages (refinementDataHistoryField stages history 0)) T
      stages history
      (refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T) =
    M.flatLimitConditions rows
      (refinementHistoryIndices stages (refinementDataHistoryField stages history 0)) T
      stages (refinementDataHistoryField stages history 7)
      (refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T) := by
  apply ZFSet.ext
  intro z
  rw [M.mem_forcingHistoryConditions, M.mem_flatLimitConditions]
  apply and_congr_right
  intro candidate
  obtain ⟨row, _, A, _, _, _, rfl⟩ := (M.mem_stageOneCandidateBound _ _ _ _).1 candidate
  rw [flatLimitConditionCode_pair, forcingHistoryConditionCode_pair_decomposition function decoded]
  exact ⟨And.left, fun cuts => ⟨cuts, recursion.tests_of_cuts
    (fun beta _ row A => forcingHistoryRawTests_successor_cut M function decoded literal commonT beta row A)
    successors row A cuts⟩⟩

theorem forcingHistoryConditions_iff_all_tests
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (ordinal : ordinalSetProperty stages)
    (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.forcingHistoryConditions rows
      (refinementHistoryIndices stages (refinementDataHistoryField stages history 0)) T
      stages history
      (refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T) ↔
    ZFSet.pair row A ∈ M.stageOneCandidateBound rows
      (refinementHistoryIndices stages (refinementDataHistoryField stages history 0)) T ∧
      ∀ beta ∈ stages, forcingHistoryRawTests M history
        (refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T)
        beta row A := by
  rw [M.forcingHistoryConditions_eq_flatLimit function decoded literal commonT successors recursion]
  exact M.flatLimitConditions_iff_all_tests pairing unions powers separation hStages
    (M.refinementDataHistoryField_mem pairing unions powers separation hStages hHistory 0)
    hT omega ordinal successors (refinementDataHistoryField_function function decoded 0)
    (refinementDataHistoryField_index_levels literal) _ recursion
    (fun beta _ row A => forcingHistoryRawTests_successor_cut M function decoded literal commonT beta row A)
    row A

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
