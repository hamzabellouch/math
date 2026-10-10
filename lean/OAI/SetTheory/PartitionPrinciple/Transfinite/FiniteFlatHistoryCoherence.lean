import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRowAssignmentTransitionFamilies
import OAI.SetTheory.PartitionPrinciple.Geometry.RefinementIndexThreeLevels
import OAI.SetTheory.PartitionPrinciple.Transfinite.RefinementHistoryPrefixLevels

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
universe u

noncomputable def finiteStageHistory (values : Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => ∅
  | n + 1 => insert (ZFSet.pair (natSetCode n) (values n)) (finiteStageHistory values n)

theorem mem_finiteStageHistory (values : Nat → ZFSet.{u}) (n : Nat) (z : ZFSet.{u}) :
    z ∈ finiteStageHistory values n ↔ ∃ i < n, z = ZFSet.pair (natSetCode i) (values i) := by
  induction n with
  | zero => simp [finiteStageHistory]
  | succ n ih =>
    rw [finiteStageHistory, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (equal | ⟨i, hi, equal⟩)
      · exact ⟨n, Nat.lt_succ_self n, equal⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, equal⟩
    · rintro ⟨i, hi, equal⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact Or.inr ⟨i, hi, equal⟩
      · exact Or.inl equal

theorem pair_mem_finiteStageHistory (values : Nat → ZFSet.{u}) (n i : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode i) y ∈ finiteStageHistory values n ↔ i < n ∧ y = values i := by
  rw [mem_finiteStageHistory]
  constructor
  · rintro ⟨j, hj, equal⟩
    obtain ⟨index, value⟩ := ZFSet.pair_inj.1 equal
    obtain rfl := natSetCode_injective index
    exact ⟨hj, value⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem finiteStageHistory_function (values : Nat → ZFSet.{u}) (n : Nat) :
    FunctionGraphOn (natSetCode n) (finiteStageHistory values n) := by
  induction n with
  | zero => exact FunctionGraphOn.empty
  | succ n ih =>
    rw [natSetCode_succ, finiteStageHistory]
    exact ih.insert (ZFSet.mem_irrefl _) (values n)

theorem finiteStageHistory_restrict (values : Nat → ZFSet.{u}) {m n : Nat} (below : m ≤ n) :
    graphRestriction (natSetCode m) (finiteStageHistory values n) = finiteStageHistory values m := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨i, hi, equal⟩ := (mem_finiteStageHistory values n _).1 entry
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact (pair_mem_finiteStageHistory values m i _).2 ⟨(natSetCode_mem_iff i m).1 hx, rfl⟩
  · intro hz
    obtain ⟨i, hi, rfl⟩ := (mem_finiteStageHistory values m z).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(pair_mem_finiteStageHistory values n i _).2 ⟨Nat.lt_of_lt_of_le hi below, rfl⟩,
        (natSetCode_mem_iff i m).2 hi⟩

theorem finiteStageHistory_congr {values other : Nat → ZFSet.{u}} (n : Nat)
    (same : ∀ i < n, values i = other i) : finiteStageHistory values n = finiteStageHistory other n := by
  apply ZFSet.ext
  intro z
  rw [mem_finiteStageHistory, mem_finiteStageHistory]
  constructor
  · rintro ⟨i, hi, equal⟩
    exact ⟨i, hi, equal.trans (congrArg (ZFSet.pair (natSetCode i)) (same i hi))⟩
  · rintro ⟨i, hi, equal⟩
    exact ⟨i, hi, equal.trans (congrArg (ZFSet.pair (natSetCode i)) (same i hi).symm)⟩

theorem flatHistoryCuts_finite_iff (values : Nat → ZFSet.{u}) (n : Nat)
    (levels row A : ZFSet.{u}) :
    FlatHistoryCuts (natSetCode n) (finiteStageHistory values n) levels row A ↔
      ∀ i < n, ZFSet.pair row (assignmentCut levels (natSetCode i) A) ∈ values i := by
  constructor
  · intro valid i hi
    obtain ⟨Q, entry, member⟩ := valid (natSetCode i) ((natSetCode_mem_iff i n).2 hi)
    exact ((pair_mem_finiteStageHistory values n i Q).1 entry).2 ▸ member
  · intro valid beta hbeta
    obtain ⟨i, hi, rfl⟩ := (mem_natSetCode beta n).1 hbeta
    exact ⟨values i, (pair_mem_finiteStageHistory values n i _).2 ⟨hi, rfl⟩, valid i hi⟩

theorem finiteFlatCuts_down (values : Nat → ZFSet.{u}) (n : Nat) (levels : ZFSet.{u})
    (self : ∀ i < n, ∀ row A, ZFSet.pair row A ∈ values i →
      assignmentCut levels (natSetCode i) A = A)
    (adjacent : ∀ i, i + 1 < n → ∀ row A, ZFSet.pair row A ∈ values (i + 1) →
      ZFSet.pair row (assignmentCut levels (natSetCode i) A) ∈ values i) :
    ∀ i < n, ∀ j, j ≤ i → ∀ row A, ZFSet.pair row A ∈ values i →
      ZFSet.pair row (assignmentCut levels (natSetCode j) A) ∈ values j := by
  intro i
  induction i with
  | zero =>
    intro hi j hj row A member
    have equal : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [self 0 hi row A member]
    exact member
  | succ i ih =>
    intro hi j hj row A member
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · have below : j ≤ i := Nat.le_of_lt_succ hj
      have cut := adjacent i hi row A member
      have result := ih (Nat.lt_of_succ_lt hi) j below row
        (assignmentCut levels (natSetCode i) A) cut
      have subset : (natSetCode j : ZFSet.{u}) ⊆ natSetCode i := by
        intro z hz
        obtain ⟨k, hk, rfl⟩ := (mem_natSetCode z j).1 hz
        exact (natSetCode_mem_iff k i).2 (Nat.lt_of_lt_of_le hk below)
      rwa [assignmentCut_nested subset] at result
    · rw [self (i + 1) hi row A member]
      exact member

theorem finiteFlatCuts_history (values : Nat → ZFSet.{u}) (n : Nat) (levels : ZFSet.{u})
    (self : ∀ i < n, ∀ row A, ZFSet.pair row A ∈ values i →
      assignmentCut levels (natSetCode i) A = A)
    (adjacent : ∀ i, i + 1 < n → ∀ row A, ZFSet.pair row A ∈ values (i + 1) →
      ZFSet.pair row (assignmentCut levels (natSetCode i) A) ∈ values i)
    {i : Nat} (hi : i < n) (row A : ZFSet.{u}) (member : ZFSet.pair row A ∈ values i) :
    FlatHistoryCuts (natSetCode (i + 1)) (finiteStageHistory values (i + 1)) levels row A := by
  rw [flatHistoryCuts_finite_iff]
  intro j hj
  exact finiteFlatCuts_down values n levels self adjacent i hi j (Nat.le_of_lt_succ hj) row A member

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem finiteStageHistory_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (values : Nat → ZFSet.{u}) (n : Nat)
    (ground : ∀ i < n, values i ∈ M.sets) : finiteStageHistory values n ∈ M.sets := by
  induction n with
  | zero => exact M.empty_mem ⟨ZFSet.omega, M.omega_mem separation infinite⟩
  | succ n ih =>
    exact M.insert_mem pairing unions
      (M.orderedPair_mem pairing (M.natSetCode_mem separation infinite n)
        (ground n (Nat.lt_succ_self n)))
      (ih (fun i hi => ground i (Nat.lt_succ_of_lt hi)))

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
universe u

noncomputable def stageThreeAssignmentLevels (I0 I1 I2 T : ZFSet.{u}) : ZFSet.{u} :=
  assignmentIndexLevels ((I0 ∪ I1) ∪ I2) T (natSetCode 3)
    (refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0)

variable {I0 I1 I2 T : ZFSet.{u}}
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode I1 (natSetCode 1))
variable (third : RefinementIndexLevelCode I2 (natSetCode 2))
include first second third

theorem pair_mem_stageThreeAssignmentLevels (z level : ZFSet.{u}) :
    ZFSet.pair z level ∈ stageThreeAssignmentLevels I0 I1 I2 T ↔
      (z ∈ stageOneAssignments I0 T ∧ level = ∅) ∨
      (z ∈ stageOneAssignments I1 T ∧ level = natSetCode 1) ∨
      (z ∈ stageOneAssignments I2 T ∧ level = natSetCode 2) := by
  rw [stageThreeAssignmentLevels, pair_mem_assignmentIndexLevels]
  constructor
  · rintro ⟨i, _, u, hu, w, hw, rfl, _, entry⟩
    rcases (first.three_level_entry second third i level).1 entry with h0 | h1 | h2
    · exact Or.inl ⟨(stageOneAssignment_mem_assignments I0 T i u w).2 ⟨h0.1, hu, hw⟩, h0.2⟩
    · exact Or.inr (Or.inl ⟨(stageOneAssignment_mem_assignments I1 T i u w).2 ⟨h1.1, hu, hw⟩, h1.2⟩)
    · exact Or.inr (Or.inr ⟨(stageOneAssignment_mem_assignments I2 T i u w).2 ⟨h2.1, hu, hw⟩, h2.2⟩)
  · rintro (⟨hz, rfl⟩ | ⟨hz, rfl⟩ | ⟨hz, rfl⟩)
    · obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I0 T z).1 hz
      exact ⟨i, ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inl hi))),
        u, hu, w, hw, rfl, (natSetCode_mem_iff 0 3).2 (by decide),
        (first.three_level_entry second third i ∅).2 (Or.inl ⟨hi, rfl⟩)⟩
    · obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I1 T z).1 hz
      exact ⟨i, ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inr hi))),
        u, hu, w, hw, rfl, (natSetCode_mem_iff 1 3).2 (by decide),
        (first.three_level_entry second third i (natSetCode 1)).2 (Or.inr (Or.inl ⟨hi, rfl⟩))⟩
    · obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I2 T z).1 hz
      exact ⟨i, ZFSet.mem_union.2 (Or.inr hi),
        u, hu, w, hw, rfl, (natSetCode_mem_iff 2 3).2 (by decide),
        (first.three_level_entry second third i (natSetCode 2)).2 (Or.inr (Or.inr ⟨hi, rfl⟩))⟩

theorem stageThreeAssignmentLevels_function :
    ZFSet.IsFunc (stageOneAssignments ((I0 ∪ I1) ∪ I2) T) (natSetCode 3)
      (stageThreeAssignmentLevels I0 I1 I2 T) :=
  assignmentIndexLevels_function (first.three_level_function second third)

theorem stageThreeAssignmentLevels_eq :
    stageThreeAssignmentLevels I0 I1 I2 T =
      (ZFSet.prod (stageOneAssignments I0 T) {∅} ∪
        ZFSet.prod (stageOneAssignments I1 T) {natSetCode 1}) ∪
        ZFSet.prod (stageOneAssignments I2 T) {natSetCode 2} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, _, level, _, rfl⟩ := ZFSet.mem_prod.1
      ((stageThreeAssignmentLevels_function first second third).1 hz)
    simpa only [ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton, or_assoc] using
      (pair_mem_stageThreeAssignmentLevels first second third x level).1 hz
  · intro hz
    rcases ZFSet.mem_union.1 hz with lower | upper
    · rcases ZFSet.mem_union.1 lower with zero | one
      · obtain ⟨x, hx, level, hl, rfl⟩ := ZFSet.mem_prod.1 zero
        exact (pair_mem_stageThreeAssignmentLevels first second third x level).2
          (Or.inl ⟨hx, ZFSet.mem_singleton.1 hl⟩)
      · obtain ⟨x, hx, level, hl, rfl⟩ := ZFSet.mem_prod.1 one
        exact (pair_mem_stageThreeAssignmentLevels first second third x level).2
          (Or.inr (Or.inl ⟨hx, ZFSet.mem_singleton.1 hl⟩))
    · obtain ⟨x, hx, level, hl, rfl⟩ := ZFSet.mem_prod.1 upper
      exact (pair_mem_stageThreeAssignmentLevels first second third x level).2
        (Or.inr (Or.inr ⟨hx, ZFSet.mem_singleton.1 hl⟩))

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {I0 I1 I2 T : ZFSet.{u}}
include pairing unions powers separation

theorem stageThreeIndexLevels_mem (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (hI2 : I2 ∈ M.sets) :
    refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0 ∈ M.sets := by
  have h0 : natSetCode 0 ∈ M.sets := M.empty_mem ⟨I0, hI0⟩
  have h1 : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions h0 h0
  have h2 : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions h1 h1
  have h3 : natSetCode 3 ∈ M.sets := M.insert_mem pairing unions h2 h2
  exact M.refinementIndexFieldGraph_mem pairing unions powers separation
    (M.binary_union_mem pairing unions (M.binary_union_mem pairing unions hI0 hI1) hI2) h3 0

theorem stageThreeAssignmentLevels_mem (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (hI2 : I2 ∈ M.sets) (hT : T ∈ M.sets) :
    stageThreeAssignmentLevels I0 I1 I2 T ∈ M.sets := by
  have h0 : natSetCode 0 ∈ M.sets := M.empty_mem ⟨I0, hI0⟩
  have h1 : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions h0 h0
  have h2 : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions h1 h1
  have h3 : natSetCode 3 ∈ M.sets := M.insert_mem pairing unions h2 h2
  exact M.assignmentIndexLevels_mem pairing unions powers separation
    (M.binary_union_mem pairing unions (M.binary_union_mem pairing unions hI0 hI1) hI2) hT h3
    (M.stageThreeIndexLevels_mem pairing unions powers separation hI0 hI1 hI2)

theorem stageThreeLevelData (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets)
    (hI2 : I2 ∈ M.sets) (hT : T ∈ M.sets)
    (first : RefinementIndexLevelCode I0 ∅)
    (second : RefinementIndexLevelCode I1 (natSetCode 1))
    (third : RefinementIndexLevelCode I2 (natSetCode 2)) :
    ((I0 ∪ I1) ∪ I2) ∈ M.sets ∧
      refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0 ∈ M.sets ∧
      stageThreeAssignmentLevels I0 I1 I2 T ∈ M.sets ∧
      ZFSet.IsFunc ((I0 ∪ I1) ∪ I2) (natSetCode 3)
        (refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0) ∧
      ZFSet.IsFunc (stageOneAssignments ((I0 ∪ I1) ∪ I2) T) (natSetCode 3)
        (stageThreeAssignmentLevels I0 I1 I2 T) ∧
      refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0 =
        (ZFSet.prod I0 {∅} ∪ ZFSet.prod I1 {natSetCode 1}) ∪ ZFSet.prod I2 {natSetCode 2} ∧
      stageThreeAssignmentLevels I0 I1 I2 T =
        (ZFSet.prod (stageOneAssignments I0 T) {∅} ∪
          ZFSet.prod (stageOneAssignments I1 T) {natSetCode 1}) ∪
          ZFSet.prod (stageOneAssignments I2 T) {natSetCode 2} ∧
      (∀ x, ¬ (x ∈ I0 ∧ x ∈ I1)) ∧ (∀ x, ¬ (x ∈ I0 ∧ x ∈ I2)) ∧
        (∀ x, ¬ (x ∈ I1 ∧ x ∈ I2)) := by
  exact ⟨M.binary_union_mem pairing unions (M.binary_union_mem pairing unions hI0 hI1) hI2,
    M.stageThreeIndexLevels_mem pairing unions powers separation hI0 hI1 hI2,
    M.stageThreeAssignmentLevels_mem pairing unions powers separation hI0 hI1 hI2 hT,
    first.three_level_function second third, stageThreeAssignmentLevels_function first second third,
    first.three_level_graph second third, stageThreeAssignmentLevels_eq first second third,
    first.three_levels_disjoint second third⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
universe u

noncomputable def threeRefinementHistory (I0 I1 I2 : ZFSet.{u}) : ZFSet.{u} :=
  finiteStageHistory (fun | 0 => I0 | 1 => I1 | _ => I2) 3

theorem pair_mem_threeRefinementHistory (I0 I1 I2 xi I : ZFSet.{u}) :
    ZFSet.pair xi I ∈ threeRefinementHistory I0 I1 I2 ↔
      (xi = natSetCode 0 ∧ I = I0) ∨ (xi = natSetCode 1 ∧ I = I1) ∨
        (xi = natSetCode 2 ∧ I = I2) := by
  simp only [threeRefinementHistory, finiteStageHistory, ZFSet.mem_insert_iff,
    ZFSet.notMem_empty, or_false, ZFSet.pair_inj]
  constructor
  · rintro (h2 | h1 | h0)
    · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h0
  · rintro (h0 | h1 | h2)
    · exact Or.inr (Or.inr h0)
    · exact Or.inr (Or.inl h1)
    · exact Or.inl h2

theorem threeRefinementHistory_function (I0 I1 I2 : ZFSet.{u}) :
    FunctionGraphOn (natSetCode 3) (threeRefinementHistory I0 I1 I2) :=
  finiteStageHistory_function _ 3

theorem threeRefinementHistory_literal {I0 I1 I2 : ZFSet.{u}}
    (first : RefinementIndexLevelCode I0 ∅)
    (second : RefinementIndexLevelCode I1 (natSetCode 1))
    (third : RefinementIndexLevelCode I2 (natSetCode 2)) :
    ∀ xi I, ZFSet.pair xi I ∈ threeRefinementHistory I0 I1 I2 → RefinementIndexLevelCode I xi := by
  intro xi I entry
  rcases (pair_mem_threeRefinementHistory I0 I1 I2 xi I).1 entry with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact first
  · exact second
  · exact third

theorem threeRefinementHistory_indices (I0 I1 I2 : ZFSet.{u}) :
    refinementHistoryIndices (natSetCode 3) (threeRefinementHistory I0 I1 I2) = (I0 ∪ I1) ∪ I2 := by
  apply ZFSet.ext
  intro x
  rw [mem_refinementHistoryIndices, ZFSet.mem_union, ZFSet.mem_union]
  constructor
  · rintro ⟨xi, _, I, entry, hi⟩
    rcases (pair_mem_threeRefinementHistory I0 I1 I2 xi I).1 entry with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  · have h0 := (pair_mem_threeRefinementHistory I0 I1 I2 (natSetCode 0) I0).2
      (Or.inl ⟨rfl, rfl⟩)
    have h1 := (pair_mem_threeRefinementHistory I0 I1 I2 (natSetCode 1) I1).2
      (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have h2 := (pair_mem_threeRefinementHistory I0 I1 I2 (natSetCode 2) I2).2
      (Or.inr (Or.inr ⟨rfl, rfl⟩))
    have function := threeRefinementHistory_function I0 I1 I2
    rintro ((hi | hi) | hi)
    · exact ⟨natSetCode 0, function.pair_source h0, I0, h0, hi⟩
    · exact ⟨natSetCode 1, function.pair_source h1, I1, h1, hi⟩
    · exact ⟨natSetCode 2, function.pair_source h2, I2, h2, hi⟩

theorem threeRefinementHistory_levels (I0 I1 I2 : ZFSet.{u}) :
    refinementHistoryLevels (natSetCode 3) (threeRefinementHistory I0 I1 I2) =
      refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) (natSetCode 3) 0 := by
  rw [refinementHistoryLevels, threeRefinementHistory_indices]

theorem threeRefinementHistory_assignmentLevels (I0 I1 I2 T : ZFSet.{u}) :
    refinementHistoryAssignmentLevels (natSetCode 3) (threeRefinementHistory I0 I1 I2) T =
      stageThreeAssignmentLevels I0 I1 I2 T := by
  rw [refinementHistoryAssignmentLevels, threeRefinementHistory_indices, threeRefinementHistory_levels]
  rfl

theorem threeRefinementHistory_anchors (I0 I1 I2 B : ZFSet.{u}) :
    refinementIndexFieldGraph
        (refinementHistoryIndices (natSetCode 3) (threeRefinementHistory I0 I1 I2)) B 2 =
      refinementIndexFieldGraph ((I0 ∪ I1) ∪ I2) B 2 := by
  rw [threeRefinementHistory_indices]

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u

theorem threeRefinementHistory_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {I0 I1 I2 : ZFSet.{u}} (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets) (hI2 : I2 ∈ M.sets) :
    threeRefinementHistory I0 I1 I2 ∈ M.sets := by
  have h0 : natSetCode 0 ∈ M.sets := M.empty_mem ⟨I0, hI0⟩
  have h1 : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions h0 h0
  have h2 : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions h1 h1
  exact M.insert_mem pairing unions (M.orderedPair_mem pairing h2 hI2)
    (M.insert_mem pairing unions (M.orderedPair_mem pairing h1 hI1)
      (M.insert_mem pairing unions (M.orderedPair_mem pairing h0 hI0) h0))

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
universe u

structure FiniteFlatHistoryCoherence (M : TransitiveGround.{u}) (values : Nat → ZFSet.{u})
    (n : Nat) (levels : ZFSet.{u}) : Prop where
  stages_ground : natSetCode n ∈ M.sets
  history_ground : finiteStageHistory values n ∈ M.sets
  levels_ground : levels ∈ M.sets
  flat : ∀ i < n, ∀ z ∈ values i, ∃ row A, z = ZFSet.pair row A
  downward : ∀ i < n, ∀ j, j ≤ i → ∀ row A, ZFSet.pair row A ∈ values i →
    ZFSet.pair row (assignmentCut levels (natSetCode j) A) ∈ values j
  transition_ground : M.rowAssignmentTransitionFamily (natSetCode n)
    (finiteStageHistory values n) levels ∈ M.sets
  transition_function : ZFSet.IsFunc (ZFSet.prod (natSetCode n) (natSetCode n))
    (M.groundRelations (⋃₀ ⋃₀ ⋃₀ (finiteStageHistory values n)) (⋃₀ ⋃₀ ⋃₀ (finiteStageHistory values n)))
    (M.rowAssignmentTransitionFamily (natSetCode n) (finiteStageHistory values n) levels)
  transition_entry : ∀ i < n, ∀ j < n, ∀ R,
    ZFSet.pair (ZFSet.pair (natSetCode i) (natSetCode j)) R ∈
      M.rowAssignmentTransitionFamily (natSetCode n) (finiteStageHistory values n) levels ↔
      R = rowAssignmentCutGraph (values i) (values j) levels (natSetCode j)
  restriction_function : ∀ i < n, ∀ j, j ≤ i →
    ZFSet.IsFunc (values i) (values j)
      (rowAssignmentCutGraph (values i) (values j) levels (natSetCode j))
  restriction_identity : ∀ i < n,
    rowAssignmentCutGraph (values i) (values i) levels (natSetCode i) = identityFunctionGraph (values i)
  restriction_compose : ∀ i < n, ∀ j, j ≤ i → ∀ k, k ≤ j →
    relationCompose (values i) (values j) (values k)
      (rowAssignmentCutGraph (values i) (values j) levels (natSetCode j))
      (rowAssignmentCutGraph (values j) (values k) levels (natSetCode k)) =
        rowAssignmentCutGraph (values i) (values k) levels (natSetCode k)

end PartitionPilot.Forcing

end OAI
