import OAI.SetTheory.PartitionPrinciple.Forcing.FlatConditionSystems
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFlatLimitConditions
import OAI.SetTheory.PartitionPrinciple.Forcing.StageTwoAssignmentTestActions

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem flatLimitConditions_restrict {rows I T stages earlier history levels z : ZFSet.{u}}
    (member : z ∈ M.flatLimitConditions rows I T stages history levels) (subset : earlier ⊆ stages) :
    z ∈ M.flatLimitConditions rows I T earlier (graphRestriction earlier history) levels := by
  obtain ⟨candidate, row, A, equal, valid⟩ := (M.mem_flatLimitConditions _ _ _ _ _ _ _).1 member
  exact (M.mem_flatLimitConditions _ _ _ _ _ _ _).2
    ⟨candidate, row, A, equal, flatHistoryCuts_restrict valid subset⟩

theorem flatLimitConditions_cut
    (separation : SeparationSchema M.sets)
    {rows I targetI T stages earlier history levels alpha row A : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (member : ZFSet.pair row A ∈ M.flatLimitConditions rows I T stages history levels)
    (subset : earlier ⊆ stages)
    (nested : ∀ beta ∈ earlier, assignmentCut levels beta (assignmentCut levels alpha A) =
      assignmentCut levels beta A)
    (target : assignmentCut levels alpha A ⊆ stageOneAssignments targetI T) :
    ZFSet.pair row (assignmentCut levels alpha A) ∈
      M.flatLimitConditions rows targetI T earlier (graphRestriction earlier history) levels := by
  obtain ⟨hrow, hA, _, small, valid⟩ := (M.pair_mem_flatLimitConditions _ _ _ _ _ _ _ _).1 member
  exact (M.pair_mem_flatLimitConditions _ _ _ _ _ _ _ _).2
    ⟨hrow, M.assignmentCut_mem separation hLevels hAlpha hA, target,
      M.assignmentCut_small separation hLevels hAlpha hA omega small,
      flatHistoryCuts_cut valid subset nested⟩

theorem flatLimitConditions_cut_of_subset
    (separation : SeparationSchema M.sets)
    {rows I targetI T stages earlier history levels alpha row A : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (member : ZFSet.pair row A ∈ M.flatLimitConditions rows I T stages history levels)
    (subset : earlier ⊆ stages) (below : ∀ beta ∈ earlier, beta ⊆ alpha)
    (target : assignmentCut levels alpha A ⊆ stageOneAssignments targetI T) :
    ZFSet.pair row (assignmentCut levels alpha A) ∈
      M.flatLimitConditions rows targetI T earlier (graphRestriction earlier history) levels :=
  M.flatLimitConditions_cut separation hLevels hAlpha omega member subset
    (fun beta hbeta => assignmentCut_nested (below beta hbeta)) target

theorem flatLimitConditions_lookup {rows I T stages history levels row A beta Q : ZFSet.{u}}
    (member : ZFSet.pair row A ∈ M.flatLimitConditions rows I T stages history levels)
    (function : FunctionGraphOn stages history) (hbeta : beta ∈ stages)
    (entry : ZFSet.pair beta Q ∈ history) :
    ZFSet.pair row (assignmentCut levels beta A) ∈ Q := by
  have valid := ((M.pair_mem_flatLimitConditions _ _ _ _ _ _ _ _).1 member).2.2.2.2
  exact (flatHistoryCuts_lookup_iff function).1 valid beta hbeta Q entry

theorem flatLimitConditions_eq_of_stage {rows I T stages history levels alpha Q : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (halpha : alpha ∈ stages)
    (entry : ZFSet.pair alpha Q ∈ history)
    (shape : Q ⊆ M.stageOneCandidateBound rows I T)
    (valid : ∀ row A, ZFSet.pair row A ∈ Q → FlatHistoryCuts stages history levels row A)
    (full : ∀ row A, ZFSet.pair row A ∈ M.stageOneCandidateBound rows I T →
      assignmentCut levels alpha A = A) :
    M.flatLimitConditions rows I T stages history levels = Q := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    have candidate := ((M.mem_flatLimitConditions _ _ _ _ _ _ _).1 member).1
    obtain ⟨row, _, A, _, _, _, rfl⟩ := (M.mem_stageOneCandidateBound rows I T z).1 candidate
    have lower := M.flatLimitConditions_lookup member function halpha entry
    exact full row A candidate ▸ lower
  · intro member
    have candidate := shape member
    obtain ⟨row, _, A, _, _, _, equal⟩ := (M.mem_stageOneCandidateBound rows I T z).1 candidate
    exact (M.mem_flatLimitConditions _ _ _ _ _ _ _).2
      ⟨candidate, row, A, equal, valid row A (equal ▸ member)⟩

end TransitiveGround

section
universe u
variable {I0 I1 I2 T : ZFSet.{u}}
variable (first : RefinementIndexLevelCode I0 ∅)
    (second : RefinementIndexLevelCode I1 (natSetCode 1))
    (third : RefinementIndexLevelCode I2 (natSetCode 2))
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T
include first second third

theorem stageThreeAssignmentCut_nat (n : Nat) (A : ZFSet.{u}) :
    assignmentCut levels (natSetCode n) A =
      ZFSet.sep (fun z => (z ∈ stageOneAssignments I0 T ∧ 0 < n) ∨
        (z ∈ stageOneAssignments I1 T ∧ 1 < n) ∨
        (z ∈ stageOneAssignments I2 T ∧ 2 < n)) A := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, ZFSet.mem_sep]
  constructor
  · rintro ⟨hz, level, hl, entry⟩
    rcases (pair_mem_stageThreeAssignmentLevels first second third z level).1 entry with
      ⟨h0, rfl⟩ | ⟨h1, rfl⟩ | ⟨h2, rfl⟩
    · exact ⟨hz, Or.inl ⟨h0, (natSetCode_mem_iff 0 n).1 hl⟩⟩
    · exact ⟨hz, Or.inr (Or.inl ⟨h1, (natSetCode_mem_iff 1 n).1 hl⟩)⟩
    · exact ⟨hz, Or.inr (Or.inr ⟨h2, (natSetCode_mem_iff 2 n).1 hl⟩)⟩
  · rintro ⟨hz, h0 | h1 | h2⟩
    · exact ⟨hz, natSetCode 0, (natSetCode_mem_iff 0 n).2 h0.2,
        (pair_mem_stageThreeAssignmentLevels first second third z _).2 (Or.inl ⟨h0.1, rfl⟩)⟩
    · exact ⟨hz, natSetCode 1, (natSetCode_mem_iff 1 n).2 h1.2,
        (pair_mem_stageThreeAssignmentLevels first second third z _).2 (Or.inr (Or.inl ⟨h1.1, rfl⟩))⟩
    · exact ⟨hz, natSetCode 2, (natSetCode_mem_iff 2 n).2 h2.2,
        (pair_mem_stageThreeAssignmentLevels first second third z _).2 (Or.inr (Or.inr ⟨h2.1, rfl⟩))⟩

theorem stageThreeAssignmentCut_one (A : ZFSet.{u}) :
    assignmentCut levels (natSetCode 1) A =
      ZFSet.sep (fun z => z ∈ stageOneAssignments I0 T) A := by
  rw [stageThreeAssignmentCut_nat first second third]
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_sep]
  simp

theorem stageThreeAssignmentCut_two (A : ZFSet.{u}) :
    assignmentCut levels (natSetCode 2) A =
      ZFSet.sep (fun z => z ∈ stageOneAssignments (I0 ∪ I1) T) A := by
  rw [stageThreeAssignmentCut_nat first second third, stageOneAssignments_union]
  apply ZFSet.ext
  intro z
  simp only [ZFSet.mem_sep, ZFSet.mem_union]
  simp

theorem stageThreeAssignmentCut_three {A : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments ((I0 ∪ I1) ∪ I2) T) :
    assignmentCut levels (natSetCode 3) A = A :=
  assignmentCut_full (stageThreeAssignmentLevels_function first second third) subset

theorem stageThreeAssignmentCut_two_eq {A : ZFSet.{u}}
    (subset : A ⊆ stageOneAssignments (I0 ∪ I1) T) :
    assignmentCut levels (natSetCode 2) A = A := by
  rw [stageThreeAssignmentCut_two first second third]
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => (ZFSet.mem_sep.1 hz).1, fun hz => ZFSet.mem_sep.2 ⟨hz, subset hz⟩⟩

theorem stageThreeAssignmentCut_one_old (A : ZFSet.{u}) :
    assignmentCut levels (natSetCode 1) A =
      assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) A := by
  rw [stageThreeAssignmentCut_one first second third, stageTwoAssignmentCut_one first second]

theorem stageThreeAssignmentCut_nested (A : ZFSet.{u}) :
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1)
      (assignmentCut levels (natSetCode 2) A) = assignmentCut levels (natSetCode 1) A := by
  rw [← stageThreeAssignmentCut_one_old first second third]
  exact assignmentCut_nested (show (natSetCode 1 : ZFSet.{u}) ⊆ natSetCode 2 from
    fun _ hx => by
      rw [natSetCode_succ]
      exact ZFSet.mem_insert_of_mem _ hx)

end

section
open SetRealization
universe u

def fourFlatStageValues (Q0 Q1 Q2 Q3 : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => Q0
  | 1 => Q1
  | 2 => Q2
  | _ => Q3

private theorem flatCoordinates {M : TransitiveGround.{u}} {R P : Type u}
    [PartialOrder R] [PartialOrder P] {c : Presentation R} {s : Presentation P} {J : ZFSet.{u}}
    (F : FlatConditionSystem M c s J) {row A : ZFSet.{u}}
    (member : ZFSet.pair row A ∈ s.carrier) :
    ∃ p : P, c.encode (F.row p) = row ∧ F.assignments p = A := by
  obtain ⟨p, equal⟩ := (s.mem_carrier _).1 member
  rw [F.encode] at equal
  exact ⟨p, ZFSet.pair_inj.1 equal⟩

variable (M : TransitiveGround.{u}) {R P1 P2 P3 : Type u}
variable [PartialOrder R] [PartialOrder P1] [PartialOrder P2] [PartialOrder P3]
variable (c : Presentation R) (s1 : Presentation P1) (s2 : Presentation P2) (s3 : Presentation P3)
variable (I0 I1 I2 T : ZFSet.{u})
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode I1 (natSetCode 1))
variable (third : RefinementIndexLevelCode I2 (natSetCode 2))
variable (F1 : FlatConditionSystem M c s1 (stageOneAssignments I0 T))
variable (F2 : FlatConditionSystem M c s2 (stageOneAssignments (I0 ∪ I1) T))
variable (F3 : FlatConditionSystem M c s3 (stageOneAssignments ((I0 ∪ I1) ∪ I2) T))
local notation "values" => fourFlatStageValues c.pairEmpty.carrier s1.carrier s2.carrier s3.carrier
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T

include F1 F2 F3

theorem fourFlatStageValues_flat :
    ∀ i < 4, ∀ z ∈ values i, ∃ row A, z = ZFSet.pair row A := by
  intro i hi z hz
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · obtain ⟨p, rfl⟩ := (c.pairEmpty.mem_carrier z).1 hz
    exact ⟨c.encode p, ∅, rfl⟩
  · obtain ⟨p, rfl⟩ := (s1.mem_carrier z).1 hz
    exact ⟨c.encode (F1.row p), F1.assignments p, F1.encode p⟩
  · obtain ⟨p, rfl⟩ := (s2.mem_carrier z).1 hz
    exact ⟨c.encode (F2.row p), F2.assignments p, F2.encode p⟩
  · obtain ⟨p, rfl⟩ := (s3.mem_carrier z).1 hz
    exact ⟨c.encode (F3.row p), F3.assignments p, F3.encode p⟩

include first second third in
theorem fourFlatStageValues_self :
    ∀ i < 4, ∀ row A, ZFSet.pair row A ∈ values i →
      assignmentCut levels (natSetCode i) A = A := by
  intro i hi row A member
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · obtain ⟨p, equal⟩ := (c.pairEmpty.mem_carrier _).1 member
    have pair : ZFSet.pair (c.encode p) ∅ = ZFSet.pair row A := equal
    obtain ⟨_, rfl⟩ := ZFSet.pair_inj.1 pair
    apply ZFSet.ext
    intro z
    simp only [mem_assignmentCut, ZFSet.notMem_empty, false_and]
  · obtain ⟨p, _, rfl⟩ := flatCoordinates F1 member
    have subset := ((M.mem_groundSmallSubsets _ _ _).1 (F1.assignments_mem p)).2.1
    rw [stageThreeAssignmentCut_one first second third]
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => (ZFSet.mem_sep.1 hz).1, fun hz => ZFSet.mem_sep.2 ⟨hz, subset hz⟩⟩
  · obtain ⟨p, _, rfl⟩ := flatCoordinates F2 member
    exact stageThreeAssignmentCut_two_eq first second third
      ((M.mem_groundSmallSubsets _ _ _).1 (F2.assignments_mem p)).2.1
  · obtain ⟨p, _, rfl⟩ := flatCoordinates F3 member
    exact stageThreeAssignmentCut_three first second third
      ((M.mem_groundSmallSubsets _ _ _).1 (F3.assignments_mem p)).2.1

variable (r21 : P2 → P1) (r32 : P3 → P2)
variable (code21 : ∀ p, s1.encode (r21 p) = ZFSet.pair (c.encode (F2.row p))
  (assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) (F2.assignments p)))
variable (code32 : ∀ p, s2.encode (r32 p) = ZFSet.pair (c.encode (F3.row p))
  (assignmentCut (stageThreeAssignmentLevels I0 I1 I2 T) (natSetCode 2) (F3.assignments p)))
include F1 code21 code32 first second third

theorem fourFlatStageValues_adjacent :
    ∀ i, i + 1 < 4 → ∀ row A, ZFSet.pair row A ∈ values (i + 1) →
      ZFSet.pair row (assignmentCut levels (natSetCode i) A) ∈ values i := by
  intro i hi row A member
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · obtain ⟨p, rfl, rfl⟩ := flatCoordinates F1 member
    have empty : assignmentCut levels (natSetCode 0) (F1.assignments p) = ∅ := by
      apply ZFSet.ext
      intro z
      simp only [mem_assignmentCut, natSetCode_zero, ZFSet.notMem_empty, false_and, exists_false, and_false]
    rw [empty]
    exact c.pairEmpty.encode_mem (F1.row p)
  · obtain ⟨p, rfl, rfl⟩ := flatCoordinates F2 member
    rw [stageThreeAssignmentCut_one_old first second third]
    exact code21 p ▸ s1.encode_mem (r21 p)
  · obtain ⟨p, rfl, rfl⟩ := flatCoordinates F3 member
    exact code32 p ▸ s2.encode_mem (r32 p)

theorem fourFlatStageValues_history (row A : ZFSet.{u})
    (member : ZFSet.pair row A ∈ s3.carrier) :
    FlatHistoryCuts (natSetCode 4) (finiteStageHistory values 4) levels row A :=
  finiteFlatCuts_history values 4 levels
    (fourFlatStageValues_self M c s1 s2 s3 I0 I1 I2 T first second third F1 F2 F3)
    (fourFlatStageValues_adjacent M c s1 s2 s3 I0 I1 I2 T first second third F1 F2 F3
      r21 r32 code21 code32) (by decide : 3 < 4) row A member

end

section
universe u
variable {I0 I1 I2 T : ZFSet.{u}}
variable (first : RefinementIndexLevelCode I0 ∅)
    (second : RefinementIndexLevelCode I1 (natSetCode 1))
    (third : RefinementIndexLevelCode I2 (natSetCode 2))
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T
include first second third

theorem stageThreeAssignment_upper_not_lower {t u w : ZFSet.{u}} (upperIndex : t ∈ I2) :
    stageOneAssignment t u w ∉ stageOneAssignments (I0 ∪ I1) T := by
  intro member
  have lowerIndex := ((stageOneAssignment_mem_assignments (I0 ∪ I1) T t u w).1 member).1
  rcases ZFSet.mem_union.1 lowerIndex with h0 | h1
  · exact first.disjoint third (fun h => (by decide : (0 : Nat) ≠ 2) (natSetCode_injective h)) t
      ⟨h0, upperIndex⟩
  · exact second.disjoint third (fun h => (by decide : (1 : Nat) ≠ 2) (natSetCode_injective h)) t
      ⟨h1, upperIndex⟩

theorem stageThreeAssignment_upper_not_cut (A : ZFSet.{u}) {t u w : ZFSet.{u}}
    (upperIndex : t ∈ I2) :
    stageOneAssignment t u w ∉ assignmentCut levels (natSetCode 2) A := by
  rw [stageThreeAssignmentCut_two first second third]
  exact fun member => stageThreeAssignment_upper_not_lower first second third upperIndex
    (ZFSet.mem_sep.1 member).2

theorem stageThreeAssignmentSplice_upper_iff (Aq Ap : ZFSet.{u}) {t u w : ZFSet.{u}}
    (upperIndex : t ∈ I2) :
    stageOneAssignment t u w ∈ assignmentSplice levels (natSetCode 2) Aq Ap ↔
      stageOneAssignment t u w ∈ Ap := by
  rw [assignmentSplice, ZFSet.mem_union, assignmentUpper, ZFSet.mem_sep]
  have noLower := stageThreeAssignment_upper_not_cut (T := T) first second third Aq
    (u := u) (w := w) upperIndex
  have noOldCut := stageThreeAssignment_upper_not_cut (T := T) first second third Ap
    (u := u) (w := w) upperIndex
  exact ⟨fun h => h.elim (fun lower => False.elim (noLower lower)) And.left,
    fun member => Or.inr ⟨member, noOldCut⟩⟩

theorem stageThreeAssignment_old_no_upper {A t u w : ZFSet.{u}}
    (subsetOld : A ⊆ stageOneAssignments (I0 ∪ I1) T) (upperIndex : t ∈ I2) :
    stageOneAssignment t u w ∉ A :=
  fun member => stageThreeAssignment_upper_not_lower first second third upperIndex (subsetOld member)

theorem stageThreeAssignmentSplice_lower_eq {Aq : ZFSet.{u}} (Ap : ZFSet.{u})
    (subsetOld : Aq ⊆ stageOneAssignments (I0 ∪ I1) T) :
    assignmentCut levels (natSetCode 2) (assignmentSplice levels (natSetCode 2) Aq Ap) = Aq := by
  rw [assignmentCut_splice, stageThreeAssignmentCut_two_eq first second third subsetOld]

theorem stageThreeAssignmentSplice_first_cut (Aq Ap : ZFSet.{u}) :
    assignmentCut levels (natSetCode 1) (assignmentSplice levels (natSetCode 2) Aq Ap) =
      assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) Aq := by
  rw [assignmentCut_splice_below (show (natSetCode 1 : ZFSet.{u}) ⊆ natSetCode 2 from
    fun _ hx => by
      rw [natSetCode_succ]
      exact ZFSet.mem_insert_of_mem _ hx)]
  exact stageThreeAssignmentCut_one_old first second third Aq

theorem stageThreeAssignmentSplice_extends {Aq Ap : ZFSet.{u}}
    (subsetOld : Aq ⊆ stageOneAssignments (I0 ∪ I1) T)
    (extension : assignmentCut levels (natSetCode 2) Ap ⊆ Aq) :
    Ap ⊆ assignmentSplice levels (natSetCode 2) Aq Ap := by
  apply assignmentSplice_extends
  rw [stageThreeAssignmentCut_two_eq first second third subsetOld]
  exact extension

end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R P1 P2 P3 : Type u}
variable [PartialOrder R] [PartialOrder P1] [PartialOrder P2] [PartialOrder P3]
variable (c : Presentation R) (s1 : Presentation P1) (s2 : Presentation P2) (s3 : Presentation P3)
local notation "values" => fourFlatStageValues c.pairEmpty.carrier s1.carrier s2.carrier s3.carrier

omit [PartialOrder R] [PartialOrder P1] [PartialOrder P2] [PartialOrder P3] in
theorem fourFlatStageHistory_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (rows : c.carrier ∈ M.sets) (h1 : s1.carrier ∈ M.sets)
    (h2 : s2.carrier ∈ M.sets) (h3 : s3.carrier ∈ M.sets) :
    finiteStageHistory values 4 ∈ M.sets := by
  apply M.finiteStageHistory_mem pairing unions separation infinite
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact M.pairEmpty_carrier_mem pairing unions powers separation c rows
  · exact h1
  · exact h2
  · exact h3

variable (I0 I1 I2 T : ZFSet.{u})
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode I1 (natSetCode 1))
variable (third : RefinementIndexLevelCode I2 (natSetCode 2))
variable (F1 : FlatConditionSystem M c s1 (stageOneAssignments I0 T))
variable (F2 : FlatConditionSystem M c s2 (stageOneAssignments (I0 ∪ I1) T))
variable (F3 : FlatConditionSystem M c s3 (stageOneAssignments ((I0 ∪ I1) ∪ I2) T))
local notation "levels" => stageThreeAssignmentLevels I0 I1 I2 T
variable (r21 : P2 → P1) (r32 : P3 → P2)
variable (code21 : ∀ p, s1.encode (r21 p) = ZFSet.pair (c.encode (F2.row p))
  (assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) (F2.assignments p)))
variable (code32 : ∀ p, s2.encode (r32 p) = ZFSet.pair (c.encode (F3.row p))
  (assignmentCut (stageThreeAssignmentLevels I0 I1 I2 T) (natSetCode 2) (F3.assignments p)))
include F1 F2 F3 first second third code21 code32

theorem fourFlatStageLimit_eq :
    M.flatLimitConditions c.carrier ((I0 ∪ I1) ∪ I2) T (natSetCode 4)
      (finiteStageHistory values 4) levels = s3.carrier := by
  apply M.flatLimitConditions_eq_of_stage (finiteStageHistory_function values 4)
    ((natSetCode_mem_iff 3 4).2 (by decide))
    ((pair_mem_finiteStageHistory values 4 3 s3.carrier).2 ⟨by decide, rfl⟩)
  · intro z member
    obtain ⟨p, rfl⟩ := (s3.mem_carrier z).1 member
    rw [F3.encode p]
    obtain ⟨ground, subset, small⟩ := (M.mem_groundSmallSubsets _ _ _).1 (F3.assignments_mem p)
    exact (M.pair_mem_stageOneCandidateBound _ _ _ _ _).2
      ⟨c.encode_mem (F3.row p), ground, subset, small⟩
  · exact fourFlatStageValues_history M c s1 s2 s3 I0 I1 I2 T first second third F1 F2 F3
      r21 r32 code21 code32
  · intro row A candidate
    exact stageThreeAssignmentCut_three first second third
      ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate).2.2.1

end TransitiveGround

end PartitionPilot.Forcing

end OAI
