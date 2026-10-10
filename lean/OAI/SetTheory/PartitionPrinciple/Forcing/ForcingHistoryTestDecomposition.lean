import OAI.SetTheory.PartitionPrinciple.Geometry.RepresentativeIndexSteps
import OAI.SetTheory.PartitionPrinciple.Transfinite.RefinementHistoryPrefixLevels

namespace OAI

namespace PartitionPilot.Forcing
universe u

def ForcingHistoryConditionCode (M : TransitiveGround.{u})
    (stages history levels z : ZFSet.{u}) : Prop :=
  ∀ alpha ∈ stages, ∃ data, ZFSet.pair alpha data ∈ history ∧
    PackedSuccessorConditionCode M levels alpha data z

theorem forcingHistoryConditionCode_empty (M : TransitiveGround.{u})
    (history levels z : ZFSet.{u}) : ForcingHistoryConditionCode M ∅ history levels z :=
  fun alpha member => False.elim (ZFSet.notMem_empty alpha member)

theorem forcingHistoryConditionCode_lookup_iff {M : TransitiveGround.{u}}
    {stages history levels z : ZFSet.{u}} (function : FunctionGraphOn stages history) :
    ForcingHistoryConditionCode M stages history levels z ↔
      ∀ alpha ∈ stages, ∀ data, ZFSet.pair alpha data ∈ history →
        PackedSuccessorConditionCode M levels alpha data z := by
  constructor
  · intro valid alpha member data entry
    obtain ⟨other, old, checked⟩ := valid alpha member
    exact function.unique old entry ▸ checked
  · intro valid alpha member
    obtain ⟨data, entry⟩ := function.total member
    exact ⟨data, entry, valid alpha member data entry⟩

theorem forcingHistoryConditionCode_restrict_iff {M : TransitiveGround.{u}}
    {stages history levels z : ZFSet.{u}} :
    ForcingHistoryConditionCode M stages (graphRestriction stages history) levels z ↔
      ForcingHistoryConditionCode M stages history levels z := by
  constructor
  · intro valid alpha member
    obtain ⟨data, entry, checked⟩ := valid alpha member
    exact ⟨data, (pair_mem_graphRestriction.1 entry).1, checked⟩
  · intro valid alpha member
    obtain ⟨data, entry, checked⟩ := valid alpha member
    exact ⟨data, pair_mem_graphRestriction.2 ⟨entry, member⟩, checked⟩

theorem forcingHistoryConditionCode_mono {M : TransitiveGround.{u}}
    {stages earlier history levels z : ZFSet.{u}}
    (valid : ForcingHistoryConditionCode M stages history levels z) (subset : earlier ⊆ stages) :
    ForcingHistoryConditionCode M earlier (graphRestriction earlier history) levels z := by
  apply forcingHistoryConditionCode_restrict_iff.2
  exact fun alpha member => valid alpha (subset member)

theorem forcingHistoryConditionCode_insert_iff {M : TransitiveGround.{u}}
    {stages history levels alpha data z : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (outside : alpha ∉ stages) :
    ForcingHistoryConditionCode M (insert alpha stages)
      (insert (ZFSet.pair alpha data) history) levels z ↔
      ForcingHistoryConditionCode M stages history levels z ∧
        PackedSuccessorConditionCode M levels alpha data z := by
  constructor
  · intro valid
    constructor
    · intro beta member
      obtain ⟨value, entry, checked⟩ := valid beta (ZFSet.mem_insert_of_mem alpha member)
      rcases ZFSet.mem_insert_iff.1 entry with equal | old
      · have same := (ZFSet.pair_inj.1 equal).1
        exact False.elim (outside (same ▸ member))
      · exact ⟨value, old, checked⟩
    · obtain ⟨value, entry, checked⟩ := valid alpha (ZFSet.mem_insert alpha stages)
      have same := (function.insert outside data).unique entry (ZFSet.mem_insert _ _)
      exact same ▸ checked
  · rintro ⟨prior, current⟩ beta member
    rcases ZFSet.mem_insert_iff.1 member with rfl | member
    · exact ⟨data, ZFSet.mem_insert _ _, current⟩
    · obtain ⟨value, entry, checked⟩ := prior beta member
      exact ⟨value, ZFSet.mem_insert_of_mem _ entry, checked⟩

theorem stageTwoConditionCode_levels_congr (M : TransitiveGround.{u})
    (d : Fin 15 → ZFSet.{u}) (first second alpha z : ZFSet.{u})
    (cuts : ∀ A, assignmentCut first alpha A = assignmentCut second alpha A) :
    StageTwoConditionCode M first alpha d z ↔ StageTwoConditionCode M second alpha d z := by
  constructor
  · rintro ⟨row, A, equal, member, tests⟩
    rw [cuts A] at member tests
    exact ⟨row, A, equal, member, tests⟩
  · rintro ⟨row, A, equal, member, tests⟩
    rw [← cuts A] at member tests
    exact ⟨row, A, equal, member, tests⟩

theorem packedSuccessorConditionCode_levels_congr (M : TransitiveGround.{u})
    (first second alpha data z : ZFSet.{u})
    (cuts : ∀ A, assignmentCut first alpha A = assignmentCut second alpha A) :
    PackedSuccessorConditionCode M first alpha data z ↔
      PackedSuccessorConditionCode M second alpha data z := by
  constructor
  · rintro ⟨d, equal, checked⟩
    exact ⟨d, equal, (stageTwoConditionCode_levels_congr M d first second alpha z cuts).1 checked⟩
  · rintro ⟨d, equal, checked⟩
    exact ⟨d, equal, (stageTwoConditionCode_levels_congr M d first second alpha z cuts).2 checked⟩

theorem forcingHistoryConditionCode_levels_congr (M : TransitiveGround.{u})
    (stages history first second z : ZFSet.{u})
    (cuts : ∀ alpha ∈ stages, ∀ A, assignmentCut first alpha A = assignmentCut second alpha A) :
    ForcingHistoryConditionCode M stages history first z ↔
      ForcingHistoryConditionCode M stages history second z := by
  constructor
  · intro valid alpha member
    obtain ⟨data, entry, checked⟩ := valid alpha member
    exact ⟨data, entry, (packedSuccessorConditionCode_levels_congr M first second alpha data z
      (cuts alpha member)).1 checked⟩
  · intro valid alpha member
    obtain ⟨data, entry, checked⟩ := valid alpha member
    exact ⟨data, entry, (packedSuccessorConditionCode_levels_congr M first second alpha data z
      (cuts alpha member)).2 checked⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

def ForcingHistoryLevelCoverage (stages history levels : ZFSet.{u}) : Prop :=
  ∀ beta ∈ stages, ∀ d : Fin 15 → ZFSet.{u},
    ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
        ZFSet.pair (stageOneAssignment t u w) beta ∈ levels

theorem forcingHistoryConditionCode_cut_iff (M : TransitiveGround.{u})
    (stages history levels alpha row A : ZFSet.{u})
    (below : ∀ beta ∈ stages, beta ⊆ alpha)
    (covered : ∀ beta ∈ stages, ∀ d : Fin 15 → ZFSet.{u},
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
        ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
          ∃ xi ∈ alpha, ZFSet.pair (stageOneAssignment t u w) xi ∈ levels) :
    ForcingHistoryConditionCode M stages history levels (ZFSet.pair row (assignmentCut levels alpha A)) ↔
      ForcingHistoryConditionCode M stages history levels (ZFSet.pair row A) := by
  constructor
  · intro valid beta member
    obtain ⟨data, entry, d, equal, tests⟩ := valid beta member
    rw [equal] at entry
    refine ⟨refinementFormulaDataCode d, entry, d, rfl, ?_⟩
    exact (stageTwoConditionCode_cut_iff M d levels beta alpha row A (below beta member)
      (covered beta member d entry)).1 tests
  · intro valid beta member
    obtain ⟨data, entry, d, equal, tests⟩ := valid beta member
    rw [equal] at entry
    refine ⟨refinementFormulaDataCode d, entry, d, rfl, ?_⟩
    exact (stageTwoConditionCode_cut_iff M d levels beta alpha row A (below beta member)
      (covered beta member d entry)).2 tests

theorem forcingHistoryConditionCode_ordinalCut_iff (M : TransitiveGround.{u})
    (stages history levels alpha row A : ZFSet.{u})
    (ordinal : ordinalSetProperty alpha) (subset : stages ⊆ alpha)
    (coverage : ForcingHistoryLevelCoverage stages history levels) :
    ForcingHistoryConditionCode M stages history levels (ZFSet.pair row (assignmentCut levels alpha A)) ↔
      ForcingHistoryConditionCode M stages history levels (ZFSet.pair row A) := by
  apply forcingHistoryConditionCode_cut_iff M stages history levels alpha row A
  · intro beta member xi hxi
    exact ordinal.1 beta (subset member) xi hxi
  · intro beta member d entry t ht u hu w hw
    exact ⟨beta, subset member, coverage beta member d entry t ht u hu w hw⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
universe u

def forcingHistoryRawTests (M : TransitiveGround.{u})
    (history levels beta row A : ZFSet.{u}) : Prop :=
  ∀ d : Fin 15 → ZFSet.{u}, ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
    stageOneRawTests M d A (ZFSet.pair row (assignmentCut levels beta A))

theorem forcingHistoryConditionCode_pair_decomposition {M : TransitiveGround.{u}}
    {stages history levels : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (decoded : ∀ beta data, ZFSet.pair beta data ∈ history →
      ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d)
    (row A : ZFSet.{u}) :
    ForcingHistoryConditionCode M stages history levels (ZFSet.pair row A) ↔
      FlatHistoryCuts stages (refinementDataHistoryField stages history 7) levels row A ∧
        ∀ beta ∈ stages, forcingHistoryRawTests M history levels beta row A := by
  have carriers := refinementDataHistoryField_function function decoded 7
  constructor
  · intro valid
    have lookup := forcingHistoryConditionCode_lookup_iff function |>.1 valid
    constructor
    · intro beta hbeta
      obtain ⟨data, entry⟩ := function.total hbeta
      obtain ⟨d, rfl⟩ := decoded beta data entry
      have checked := (packedSuccessorConditionCode_code_iff M levels beta d _).1
        (lookup beta hbeta _ entry)
      exact ⟨d 7, (refinementDataHistoryField_entry function d entry 7 _).2 rfl,
        ((stageTwoConditionCode_pair_iff M d levels beta row A).1 checked).1⟩
    · intro beta hbeta d entry
      have checked := (packedSuccessorConditionCode_code_iff M levels beta d _).1
        (lookup beta hbeta _ entry)
      exact ((stageTwoConditionCode_pair_iff M d levels beta row A).1 checked).2
  · rintro ⟨cuts, tests⟩ beta hbeta
    obtain ⟨data, entry⟩ := function.total hbeta
    obtain ⟨d, rfl⟩ := decoded beta data entry
    refine ⟨_, entry, (packedSuccessorConditionCode_code_iff M levels beta d _).2 ?_⟩
    apply (stageTwoConditionCode_pair_iff M d levels beta row A).2
    exact ⟨(flatHistoryCuts_lookup_iff carriers).1 cuts beta hbeta (d 7)
      ((refinementDataHistoryField_entry function d entry 7 _).2 rfl), tests beta hbeta d entry⟩

theorem forcingHistoryRawTests_cut_iff (M : TransitiveGround.{u})
    (history levels beta gamma row A : ZFSet.{u}) (below : beta ⊆ gamma)
    (covered : ∀ d : Fin 15 → ZFSet.{u}, ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
        ∃ xi ∈ gamma, ZFSet.pair (stageOneAssignment t u w) xi ∈ levels) :
    forcingHistoryRawTests M history levels beta row (assignmentCut levels gamma A) ↔
      forcingHistoryRawTests M history levels beta row A := by
  unfold forcingHistoryRawTests
  rw [assignmentCut_nested below]
  apply forall_congr'
  intro d
  apply forall_congr'
  intro entry
  exact stageOneRawTests_cut_iff M d levels gamma A _ (covered d entry)

end PartitionPilot.Forcing

end OAI
