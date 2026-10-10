import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRefinementBinaryUnions

namespace OAI

section

namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable {alpha p Ap q Aq : ZFSet.{u}}
local notation "levels" => refinementDataHistoryLevels stages history T
local notation "spliced" => assignmentSplice levels alpha Aq Ap
include run

theorem splice_mem_of_candidates (ordinal : ordinalSetProperty stages)
    (cutOrdinal : ordinalSetProperty alpha) (cutSubset : alpha ⊆ stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ A lower stronger, stageOneRawTests M d A lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d A stronger)
    (upper : ZFSet.pair p Ap ∈ M.refinementHistoryForcing rows T stages history)
    (lower : ZFSet.pair q Aq ∈ M.refinementHistoryForcing rows T alpha (graphRestriction alpha history))
    (rowsBelow : ZFSet.pair q p ∈ rowOrder)
    (contains : assignmentCut levels alpha Ap ⊆ assignmentCut levels alpha Aq)
    (candidate : ZFSet.pair q spliced ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T)
    (candidates : ∀ gamma ∈ stages, ZFSet.pair q (assignmentCut levels gamma spliced) ∈
      M.stageOneCandidateBound rows
        (refinementDataHistoryIndices gamma (graphRestriction gamma history)) T) :
    ZFSet.pair q spliced ∈ M.refinementHistoryForcing rows T stages history := by
  have dataExtended : Ap ⊆ spliced := assignmentSplice_extends contains
  have oldTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 upper).2
  have lowerTests := ((M.mem_refinementHistoryForcing rows T alpha (graphRestriction alpha history) _).1 lower).2
  have step (beta : ZFSet.{u}) (hbeta : beta ∈ stages) (d : Fin 15 → ZFSet.{u})
      (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
      (proved : ZFSet.pair q (assignmentCut levels beta spliced) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history)) :
      stageOneRawTests M d spliced (ZFSet.pair q (assignmentCut levels beta spliced)) := by
    by_cases inside : beta ∈ alpha
    · have stored := (forcingHistoryConditionCode_lookup_iff
        (run.carriers.data.function.restrict cutSubset)).1 lowerTests beta inside
        (refinementFormulaDataCode d) (pair_mem_graphRestriction.2 ⟨entry, inside⟩)
      have checked := (stageTwoConditionCode_pair_iff M d _ beta q Aq).1
        ((packedSuccessorConditionCode_code_iff M _ beta d _).1 stored)
      have sameCut := run.carriers.data.prefix_cut cutSubset (cutOrdinal.1 beta inside) Aq
      rw [sameCut] at checked
      have sameSplice : assignmentCut levels beta spliced = assignmentCut levels beta Aq :=
        assignmentCut_splice_below (cutOrdinal.1 beta inside) Aq Ap
      rw [sameSplice]
      exact (run.carriers.data.rawTests_splice_below entry M alpha Aq Ap _ inside).2 checked.2
    · have stored := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 oldTests
        beta hbeta (refinementFormulaDataCode d) entry
      have checked := (stageTwoConditionCode_pair_iff M d _ beta p Ap).1
        ((packedSuccessorConditionCode_code_iff M _ beta d _).1 stored)
      have order : ZFSet.pair (ZFSet.pair q (assignmentCut levels beta spliced))
          (ZFSet.pair p (assignmentCut levels beta Ap)) ∈ d 8 := by
        rw [run.order beta d entry]
        exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
          _ _ _ _).2 ⟨proved, run.carriers.cut_mem upper hbeta, rowsBelow, assignmentCut_mono dataExtended⟩
      exact (run.carriers.data.rawTests_splice_above entry M alpha Aq Ap _ inside).2
        (mono beta d entry Ap _ _ checked.2 order)
  have earlier : ∀ gamma ∈ stages, ZFSet.pair q (assignmentCut levels gamma spliced) ∈
      M.refinementHistoryForcing rows T gamma (graphRestriction gamma history) := by
    intro gamma
    induction gamma using ZFSet.inductionOn with
    | h gamma ih =>
      intro hgamma
      apply (M.mem_refinementHistoryForcing rows T gamma (graphRestriction gamma history) _).2
      refine ⟨candidates gamma hgamma, ?_⟩
      intro beta hbeta
      have betaFull := ordinal.1 gamma hgamma beta hbeta
      have betaSubset := ordinal.2 gamma hgamma beta hbeta
      obtain ⟨data, entry⟩ := run.carriers.data.function.total betaFull
      obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
      have proved := ih beta hbeta betaFull
      have sameCut := run.carriers.data.prefix_cut (ordinal.1 gamma hgamma) betaSubset
        (assignmentCut levels gamma spliced)
      refine ⟨refinementFormulaDataCode d, pair_mem_graphRestriction.2 ⟨entry, hbeta⟩, ?_⟩
      apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
      apply (stageTwoConditionCode_pair_iff M d _ beta q _).2
      rw [sameCut, assignmentCut_nested betaSubset]
      refine ⟨(run.carriers.carrier beta d entry).symm ▸ proved, ?_⟩
      exact stageOneRawTests_transfer M d _ (step beta betaFull d entry proved)
        (fun _ _ _ _ _ _ member => assignmentCut_subset levels gamma spliced member)
  apply (M.mem_refinementHistoryForcing rows T stages history _).2
  refine ⟨candidate, ?_⟩
  intro beta hbeta
  obtain ⟨data, entry⟩ := run.carriers.data.function.total hbeta
  obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
  refine ⟨refinementFormulaDataCode d, entry, ?_⟩
  apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
  apply (stageTwoConditionCode_pair_iff M d _ beta q _).2
  exact ⟨(run.carriers.carrier beta d entry).symm ▸ earlier beta hbeta,
    step beta hbeta d entry (earlier beta hbeta)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory



namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
local notation "levels" => refinementDataHistoryLevels stages history T
include run

theorem union_lower_bound_of_candidates (ordinal : ordinalSetProperty stages)
    (unionTests : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ (family lower : Nat → ZFSet.{u}) q,
        (∀ n m, n ≤ m → family n ⊆ family m) →
        (∀ n, ZFSet.pair q (lower n) ∈ d 8) →
        (∀ n, stageOneRawTests M d (family n) (lower n)) →
        stageOneRawTests M d (stageOneAssignmentUnion family) q)
    (family row : Nat → ZFSet.{u}) (q : ZFSet.{u})
    (members : ∀ n, ZFSet.pair (row n) (family n) ∈ M.refinementHistoryForcing rows T stages history)
    (increasing : ∀ n m, n ≤ m → family n ⊆ family m)
    (rowsBelow : ∀ n, ZFSet.pair q (row n) ∈ rowOrder)
    (candidate : ZFSet.pair q (stageOneAssignmentUnion family) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T)
    (candidates : ∀ gamma ∈ stages,
      ZFSet.pair q (assignmentCut levels gamma (stageOneAssignmentUnion family)) ∈
        M.stageOneCandidateBound rows (refinementDataHistoryIndices gamma (graphRestriction gamma history)) T) :
    ZFSet.pair q (stageOneAssignmentUnion family) ∈ M.refinementHistoryForcing rows T stages history ∧
      ∀ n, ZFSet.pair (ZFSet.pair q (stageOneAssignmentUnion family)) (ZFSet.pair (row n) (family n)) ∈
        M.refinementHistoryOrder rows rowOrder T stages history := by
  have step (beta : ZFSet.{u}) (hbeta : beta ∈ stages) (d : Fin 15 → ZFSet.{u})
      (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
      (proved : ZFSet.pair q (assignmentCut levels beta (stageOneAssignmentUnion family)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history)) :
      stageOneRawTests M d (stageOneAssignmentUnion family)
        (ZFSet.pair q (assignmentCut levels beta (stageOneAssignmentUnion family))) := by
    apply unionTests beta d entry family
      (fun n => ZFSet.pair (row n) (assignmentCut levels beta (family n))) _ increasing
    · intro n
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem (members n) hbeta, rowsBelow n,
          assignmentCut_mono (stageOneAssignmentUnion_contains family n)⟩
    · intro n
      have oldTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 (members n)).2
      have stored := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 oldTests
        beta hbeta (refinementFormulaDataCode d) entry
      exact ((stageTwoConditionCode_pair_iff M d _ beta (row n) (family n)).1
        ((packedSuccessorConditionCode_code_iff M _ beta d _).1 stored)).2
  have earlier : ∀ gamma ∈ stages,
      ZFSet.pair q (assignmentCut levels gamma (stageOneAssignmentUnion family)) ∈
        M.refinementHistoryForcing rows T gamma (graphRestriction gamma history) := by
    intro gamma
    induction gamma using ZFSet.inductionOn with
    | h gamma ih =>
      intro hgamma
      apply (M.mem_refinementHistoryForcing rows T gamma (graphRestriction gamma history) _).2
      refine ⟨candidates gamma hgamma, ?_⟩
      intro beta hbeta
      have betaFull := ordinal.1 gamma hgamma beta hbeta
      have betaSubset := ordinal.2 gamma hgamma beta hbeta
      obtain ⟨data, entry⟩ := run.carriers.data.function.total betaFull
      obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
      have proved := ih beta hbeta betaFull
      have sameCut := run.carriers.data.prefix_cut (ordinal.1 gamma hgamma) betaSubset
        (assignmentCut levels gamma (stageOneAssignmentUnion family))
      refine ⟨refinementFormulaDataCode d, pair_mem_graphRestriction.2 ⟨entry, hbeta⟩, ?_⟩
      apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
      apply (stageTwoConditionCode_pair_iff M d _ beta q _).2
      rw [sameCut, assignmentCut_nested betaSubset]
      refine ⟨(run.carriers.carrier beta d entry).symm ▸ proved, ?_⟩
      exact stageOneRawTests_transfer M d _ (step beta betaFull d entry proved)
        (fun _ _ _ _ _ _ member => assignmentCut_subset levels gamma (stageOneAssignmentUnion family) member)
  have member : ZFSet.pair q (stageOneAssignmentUnion family) ∈ M.refinementHistoryForcing rows T stages history := by
    apply (M.mem_refinementHistoryForcing rows T stages history _).2
    refine ⟨candidate, ?_⟩
    intro beta hbeta
    obtain ⟨data, entry⟩ := run.carriers.data.function.total hbeta
    obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
    refine ⟨refinementFormulaDataCode d, entry, ?_⟩
    apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
    apply (stageTwoConditionCode_pair_iff M d _ beta q _).2
    exact ⟨(run.carriers.carrier beta d entry).symm ▸ earlier beta hbeta,
      step beta hbeta d entry (earlier beta hbeta)⟩
  exact ⟨member, fun n => (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
    ⟨member, members n, rowsBelow n, stageOneAssignmentUnion_contains family n⟩⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

end

end OAI
