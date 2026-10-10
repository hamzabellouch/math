import OAI.SetTheory.PartitionPrinciple.Definability.RefinementDataHistoryEntryFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem birthHistory_scheduled_lookup (k : Nat) {W history : ZFSet.{u}}
    (function : ZFSet.IsFunc (natSetCode (k + 1)) W history) :
    ∃ record ∈ W,
      ZFSet.pair (natSetCode (Nat.unpair k).1) record ∈ history ∧
      ∀ other, ZFSet.pair (natSetCode (Nat.unpair k).1) other ∈ history → other = record := by
  have before : (natSetCode (Nat.unpair k).1 : ZFSet.{u}) ∈ natSetCode (k + 1) :=
    (natSetCode_mem_iff _ _).2 (Nat.lt_succ_of_le (Nat.unpair_left_le k))
  obtain ⟨record, entry, unique⟩ := function.2 _ before
  exact ⟨record, (ZFSet.pair_mem_prod.1 (function.1 entry)).2, entry, unique⟩

namespace RefinementDataHistory
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
include valid

theorem birthList_assignment_visit (assignments enumerations : Nat → ZFSet.{u})
    (shape : ∀ i, assignments i ⊆ stageOneAssignments (refinementDataHistoryIndices stages history) T)
    (retained : ∀ i k, i ≤ k → assignments i ⊆ assignments k)
    (onto : ∀ i alpha,
      alpha ∈ relationImage (assignments i) stages (refinementDataHistoryLevels stages history T) →
      ∃ j : Nat, ZFSet.pair (natSetCode j) alpha ∈ enumerations i)
    {x : ZFSet.{u}} (member : x ∈ stageOneAssignmentUnion assignments) :
    ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
      Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
      x ∈ assignments i ∧
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ history ∧
      ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages history T ∧
      alpha ∈ relationImage (assignments i) stages (refinementDataHistoryLevels stages history T) ∧
      ZFSet.pair (natSetCode j) alpha ∈ enumerations i ∧
      x ∈ assignmentOnIndices (fields 0) T (assignments (Nat.pair i j)) := by
  obtain ⟨i, born⟩ := (mem_stageOneAssignmentUnion assignments x).1 member
  obtain ⟨t, ht, first, hFirst, second, hSecond, rfl⟩ :=
    (mem_stageOneAssignments _ _ _).1 (shape i born)
  obtain ⟨alpha, hAlpha, fields, stored, index⟩ :=
    (mem_refinementDataHistoryIndices _ _ _).1 ht
  have terms := valid.terms alpha fields stored
  have level := valid.coverage alpha hAlpha fields stored t index
    first (terms.symm ▸ hFirst) second (terms.symm ▸ hSecond)
  have attained : alpha ∈ relationImage (assignments i) stages
      (refinementDataHistoryLevels stages history T) :=
    (mem_relationImage _ _ _ _).2 ⟨hAlpha, _, born, level⟩
  obtain ⟨j, scheduled⟩ := onto i alpha attained
  have before := Nat.left_le_pair i j
  exact ⟨i, j, alpha, hAlpha, fields, Nat.unpair_pair i j, before, born, stored,
    level, attained, scheduled,
    (assignmentOnIndices_entry _ _ _ _ _ _).2
      ⟨retained i (Nat.pair i j) before born, index, hFirst, hSecond⟩⟩

end RefinementDataHistory

end PartitionPilot.Forcing

end

end OAI
