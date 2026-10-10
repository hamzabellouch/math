import OAI.SetTheory.PartitionPrinciple.Geometry.AssignmentIndexLevels
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNiceRefinementVisibility

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

noncomputable def stageTwoAssignmentLevels (I0 I1 T : ZFSet.{u}) : ZFSet.{u} :=
  assignmentIndexLevels (I0 ∪ I1) T {∅, natSetCode 1}
    (refinementIndexFieldGraph (I0 ∪ I1) {∅, natSetCode 1} 0)

theorem stageTwoAssignmentCut_zero (I0 I1 T A : ZFSet.{u}) :
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 0) A = ∅ := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, natSetCode_zero]
  exact ⟨fun h => False.elim (ZFSet.notMem_empty _ h.2.choose_spec.1),
    fun hz => False.elim (ZFSet.notMem_empty z hz)⟩

variable {I0 I1 T : ZFSet.{u}}
    (first : RefinementIndexLevelCode I0 ∅)
    (second : RefinementIndexLevelCode I1 (natSetCode 1))
include first second

theorem pair_mem_stageTwoAssignmentLevels (z level : ZFSet.{u}) :
    ZFSet.pair z level ∈ stageTwoAssignmentLevels I0 I1 T ↔
      (z ∈ stageOneAssignments I0 T ∧ level = ∅) ∨
      (z ∈ stageOneAssignments I1 T ∧ level = natSetCode 1) := by
  rw [stageTwoAssignmentLevels, pair_mem_assignmentIndexLevels]
  constructor
  · rintro ⟨i, _, u, hu, w, hw, rfl, _, entry⟩
    rcases (first.union_level_entry second i level).1 entry with lower | upper
    · exact Or.inl ⟨(stageOneAssignment_mem_assignments I0 T i u w).2
        ⟨lower.1, hu, hw⟩, lower.2⟩
    · exact Or.inr ⟨(stageOneAssignment_mem_assignments I1 T i u w).2
        ⟨upper.1, hu, hw⟩, upper.2⟩
  · rintro (⟨hz, rfl⟩ | ⟨hz, rfl⟩)
    · obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I0 T z).1 hz
      refine ⟨i, ZFSet.mem_union.2 (Or.inl hi), u, hu, w, hw, rfl,
        ZFSet.mem_insert _ _, ?_⟩
      exact (first.union_level_entry second i ∅).2 (Or.inl ⟨hi, rfl⟩)
    · obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I1 T z).1 hz
      refine ⟨i, ZFSet.mem_union.2 (Or.inr hi), u, hu, w, hw, rfl,
        ZFSet.mem_insert_of_mem _ (ZFSet.mem_singleton.2 rfl), ?_⟩
      exact (first.union_level_entry second i (natSetCode 1)).2 (Or.inr ⟨hi, rfl⟩)

theorem stageTwoAssignmentLevels_function :
    ZFSet.IsFunc (stageOneAssignments (I0 ∪ I1) T) {∅, natSetCode 1}
      (stageTwoAssignmentLevels I0 I1 T) :=
  assignmentIndexLevels_function (first.union_level_function second)

theorem stageTwoAssignmentLevels_eq :
    stageTwoAssignmentLevels I0 I1 T =
      ZFSet.prod (stageOneAssignments I0 T) {∅} ∪
      ZFSet.prod (stageOneAssignments I1 T) {natSetCode 1} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, _, level, _, rfl⟩ := ZFSet.mem_prod.1
      ((stageTwoAssignmentLevels_function first second).1 hz)
    simpa only [ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton] using
      (pair_mem_stageTwoAssignmentLevels first second x level).1 hz
  · intro hz
    rcases ZFSet.mem_union.1 hz with lower | upper
    · obtain ⟨x, hx, level, hl, rfl⟩ := ZFSet.mem_prod.1 lower
      exact (pair_mem_stageTwoAssignmentLevels first second x level).2
        (Or.inl ⟨hx, ZFSet.mem_singleton.1 hl⟩)
    · obtain ⟨x, hx, level, hl, rfl⟩ := ZFSet.mem_prod.1 upper
      exact (pair_mem_stageTwoAssignmentLevels first second x level).2
        (Or.inr ⟨hx, ZFSet.mem_singleton.1 hl⟩)

theorem stageTwoAssignmentCut_one (A : ZFSet.{u}) :
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) A =
      ZFSet.sep (fun z => z ∈ stageOneAssignments I0 T) A := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, ZFSet.mem_sep]
  constructor
  · rintro ⟨hz, level, hl, entry⟩
    have equal : level = ∅ := by
      change level ∈ insert (∅ : ZFSet.{u}) ∅ at hl
      simpa only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false] using hl
    subst level
    rcases (pair_mem_stageTwoAssignmentLevels first second z ∅).1 entry with lower | upper
    · exact ⟨hz, lower.1⟩
    · exact False.elim (Nat.zero_ne_one (natSetCode_injective upper.2))
  · rintro ⟨hz, lower⟩
    exact ⟨hz, ∅, ZFSet.mem_insert ∅ ∅,
      (pair_mem_stageTwoAssignmentLevels first second z ∅).2 (Or.inl ⟨lower, rfl⟩)⟩

theorem stageTwoAssignmentCut_two {A : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments (I0 ∪ I1) T) :
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 2) A = A := by
  apply assignmentCut_eq_of_lower
  intro z hz
  obtain ⟨level, entry, _⟩ := (stageTwoAssignmentLevels_function first second).2 z (subset hz)
  refine ⟨level, ?_, entry⟩
  rcases (pair_mem_stageTwoAssignmentLevels first second z level).1 entry with lower | upper
  · rw [lower.2]
    exact ZFSet.mem_insert_of_mem (natSetCode 1) (ZFSet.mem_insert ∅ ∅)
  · rw [upper.2]
    exact ZFSet.mem_insert (natSetCode 1) (natSetCode 1)

theorem stageTwoAssignmentCut_one_subset (A : ZFSet.{u}) :
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) A ⊆
      stageOneAssignments I0 T := by
  rw [stageTwoAssignmentCut_one first second]
  exact fun _ hz => (ZFSet.mem_sep.1 hz).2

theorem stageTwoAssignmentCut_one_eq {A : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments I0 T) :
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) A = A := by
  rw [stageTwoAssignmentCut_one first second]
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => (ZFSet.mem_sep.1 hz).1, fun hz => ZFSet.mem_sep.2 ⟨hz, subset hz⟩⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u
variable {I0 I1 T : ZFSet.{u}}
variable (first : RefinementIndexLevelCode I0 ∅)
    (second : RefinementIndexLevelCode I1 (natSetCode 1))
include first second

theorem stageTwoAssignment_upper_not_lower {t u w : ZFSet.{u}} (upperIndex : t ∈ I1) :
    stageOneAssignment t u w ∉ stageOneAssignments I0 T := by
  intro member
  have lowerIndex := ((stageOneAssignment_mem_assignments I0 T t u w).1 member).1
  exact first.disjoint second (fun h => Nat.zero_ne_one (natSetCode_injective h)) t
    ⟨lowerIndex, upperIndex⟩

theorem stageTwoAssignment_upper_not_cut (A : ZFSet.{u}) {t u w : ZFSet.{u}}
    (upperIndex : t ∈ I1) :
    stageOneAssignment t u w ∉
      assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) A := by
  intro member
  exact stageTwoAssignment_upper_not_lower first second upperIndex
    (stageTwoAssignmentCut_one_subset first second A member)

theorem stageTwoAssignmentSplice_upper_iff (Aq Ap : ZFSet.{u}) {t u w : ZFSet.{u}}
    (upperIndex : t ∈ I1) :
    stageOneAssignment t u w ∈
      assignmentSplice (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) Aq Ap ↔
      stageOneAssignment t u w ∈ Ap := by
  rw [assignmentSplice, ZFSet.mem_union, assignmentUpper, ZFSet.mem_sep]
  have noLower := stageTwoAssignment_upper_not_cut (T := T) first second Aq (u := u) (w := w) upperIndex
  have noOldCut := stageTwoAssignment_upper_not_cut (T := T) first second Ap (u := u) (w := w) upperIndex
  exact ⟨fun h => h.elim (fun lower => False.elim (noLower lower)) And.left,
    fun member => Or.inr ⟨member, noOldCut⟩⟩

theorem stageTwoAssignment_old_no_upper {A t u w : ZFSet.{u}}
    (subsetOld : A ⊆ stageOneAssignments I0 T) (upperIndex : t ∈ I1) :
    stageOneAssignment t u w ∉ A :=
  fun member => stageTwoAssignment_upper_not_lower first second upperIndex (subsetOld member)

theorem stageTwoAssignmentSplice_lower_eq {Aq : ZFSet.{u}} (Ap : ZFSet.{u})
    (subsetOld : Aq ⊆ stageOneAssignments I0 T) :
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1)
      (assignmentSplice (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) Aq Ap) = Aq := by
  rw [assignmentCut_splice, stageTwoAssignmentCut_one_eq first second subsetOld]

end PartitionPilot.Forcing

end

end OAI
