import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoConditionTop

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

namespace StageTwoCondition
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
local notation "levels" => stageTwoAssignmentLevels I0 (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T
local notation "B" => M.groundSmallSubsets (stageOneAssignments (I0 ∪ (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid)) T) ZFSet.omega
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets) (hI1 : (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) ∈ M.sets)
noncomputable def chainUnion (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) : Condition := by
  have old := (M.mem_groundSmallSubsets _ _ _).1 (F.assignments_mem q)
  have memberq : F.assignments q ∈ B := by
    apply (M.mem_groundSmallSubsets _ _ _).2
    refine ⟨old.1, ?_, old.2.2⟩
    intro z hz
    obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I0 T z).1 (old.2.1 hz)
    exact (stageOneAssignment_mem_assignments _ T t u w).2
      ⟨ZFSet.mem_union.2 (Or.inl ht), hu, hw⟩
  have graph := M.stageTwoAssignmentLevels_mem pairing unions powers separation hI0 hI1 hT
  have hOne := M.transitive (M.omega_mem separation infinite) (natSetCode_mem_omega 1)
  have lowerCut := stageTwoAssignmentSplice_lower_eq first second (stageOneAssignmentUnion (fun n => (seq n).assignments)) old.2.1
  exact {
    row := F.row q
    assignments := assignmentSplice levels (natSetCode 1) (F.assignments q) (stageOneAssignmentUnion (fun n => (seq n).assignments))
    assignments_mem := M.assignmentSplice_mem_groundSmallSubsets pairing unions powers separation
      infinite choice graph hOne memberq small
    lower := q
    lower_code := by rw [lowerCut]; exact F.encode q
    tests := (M.refinementLevelTests_stageTwoSplice s pairing unions powers separation collection
      carrier order hT valid a b d base directed system first second (F.assignments q) (stageOneAssignmentUnion (fun n => (seq n).assignments)) q).2
      (M.refinementLevelTests_union s pairing unions powers separation collection carrier order hT valid
        a b d base directed system (natSetCode 1) T2
        (fun n => (seq n).assignments) (fun n => (seq n).lower) q
        (fun _ _ less => (decreasing less).2) below (fun n => (seq n).tests)) }

local notation "bound" => chainUnion M c I0 a s b d T T2 valid pairing unions powers separation
  collection carrier order hT base directed system F first second infinite choice hI0 hI1

theorem chainUnion_row (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) :
    (bound seq decreasing q below small).row = F.row q := rfl

theorem chainUnion_assignments (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) :
    (bound seq decreasing q below small).assignments =
    assignmentSplice levels (natSetCode 1) (F.assignments q) (stageOneAssignmentUnion (fun n => (seq n).assignments)) := rfl

theorem chainUnion_lower (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) :
    (bound seq decreasing q below small).lower = q := rfl

theorem chainUnion_le (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) (n : Nat) :
    bound seq decreasing q below small ≤ seq n := by
  have rows := ((F.le_iff q (seq n).lower).1 (below n)).1
  have rowEqual := lower_row M c I0 a s b d T T2 valid pairing unions powers separation collection
    carrier order hT base directed system F (seq n)
  have contains : (stageOneAssignmentUnion (fun n => (seq n).assignments)) ⊆ assignmentSplice levels (natSetCode 1) (F.assignments q) (stageOneAssignmentUnion (fun n => (seq n).assignments)) := by
    apply assignmentSplice_extends
    rw [stageTwoAssignmentCut_one_eq first second
      ((M.mem_groundSmallSubsets _ _ _).1 (F.assignments_mem q)).2.1]
    intro z hz
    obtain ⟨member, level⟩ := (mem_assignmentCut levels (natSetCode 1) (stageOneAssignmentUnion (fun n => (seq n).assignments)) z).1 hz
    obtain ⟨m, hm⟩ := (mem_stageOneAssignmentUnion (fun n => (seq n).assignments) z).1 member
    have lowerMember : z ∈ F.assignments (seq m).lower := by
      rw [lower_assignments M c I0 a s b d T T2 valid pairing unions powers separation collection
        carrier order hT base directed system F (seq m)]
      exact (mem_assignmentCut levels (natSetCode 1) (seq m).assignments z).2 ⟨hm, level⟩
    exact ((F.le_iff q (seq m).lower).1 (below m)).2 lowerMember
  exact ⟨rows.trans_eq rowEqual, fun z hz => contains
    (stageOneAssignmentUnion_contains (fun n => (seq n).assignments) n hz)⟩

end StageTwoCondition
end PartitionPilot.Forcing

end

end OAI
