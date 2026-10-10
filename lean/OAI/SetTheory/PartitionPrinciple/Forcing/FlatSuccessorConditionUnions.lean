import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageThreeSuccessorLaws
import OAI.SetTheory.PartitionPrinciple.Transfinite.RefinementFlatSuccessorUnions

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)

namespace FlatSuccessorCondition
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "B" => M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega
variable {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)
variable (laws : FlatSuccessorLaws Jold I T levels alpha tests)
variable (unionLaws : FlatSuccessorUnionLaws tests)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)

noncomputable def chainUnion (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) : Condition := by
  have old := ((M.mem_groundSmallSubsets _ _ _).1 (F.assignments_mem q)).2.1
  have memberq : F.assignments q ∈ B :=
    (includeLower M c s I T levels alpha tests F laws q).assignments_mem
  exact {
    row := F.row q
    assignments := assignmentSplice levels alpha (F.assignments q)
      (stageOneAssignmentUnion (fun n => (seq n).assignments))
    assignments_mem := M.assignmentSplice_mem_groundSmallSubsets pairing unions powers separation
      infinite choice hLevels hAlpha memberq small
    lower := q
    lower_code := by rw [assignmentCut_splice, laws.cut_old _ old]; exact F.encode q
    tests := (laws.tests_splice _ _ q old).2
      (unionLaws.tests_union (fun n => (seq n).assignments) (fun n => (seq n).lower) q
        (fun _ _ less => (decreasing less).2) below (fun n => (seq n).tests)) }

local notation "bound" => chainUnion M c s I T levels alpha tests F laws unionLaws
  pairing unions powers separation infinite choice hLevels hAlpha

theorem chainUnion_row (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) :
    (bound seq decreasing q below small).row = F.row q := rfl

theorem chainUnion_assignments (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) :
    (bound seq decreasing q below small).assignments =
      assignmentSplice levels alpha (F.assignments q)
        (stageOneAssignmentUnion (fun n => (seq n).assignments)) := rfl

theorem chainUnion_lower (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) :
    (bound seq decreasing q below small).lower = q := rfl

theorem chainUnion_le (seq : Nat → Condition) (decreasing : Antitone seq) (q : P)
    (below : ∀ n, q ≤ (seq n).lower)
    (small : stageOneAssignmentUnion (fun n => (seq n).assignments) ∈ B) (n : Nat) :
    bound seq decreasing q below small ≤ seq n := by
  have rows := ((F.le_iff q (seq n).lower).1 (below n)).1
  have rowEqual := lower_row M c s I T levels alpha tests F (seq n)
  have contains : stageOneAssignmentUnion (fun n => (seq n).assignments) ⊆
      assignmentSplice levels alpha (F.assignments q)
        (stageOneAssignmentUnion (fun n => (seq n).assignments)) := by
    apply assignmentSplice_extends
    rw [laws.cut_old _ ((M.mem_groundSmallSubsets _ _ _).1 (F.assignments_mem q)).2.1]
    intro z hz
    obtain ⟨member, level⟩ := (mem_assignmentCut levels alpha
      (stageOneAssignmentUnion (fun n => (seq n).assignments)) z).1 hz
    obtain ⟨m, hm⟩ := (mem_stageOneAssignmentUnion (fun n => (seq n).assignments) z).1 member
    have lowerMember : z ∈ F.assignments (seq m).lower := by
      rw [lower_assignments M c s I T levels alpha tests F (seq m)]
      exact (mem_assignmentCut levels alpha (seq m).assignments z).2 ⟨hm, level⟩
    exact ((F.le_iff q (seq m).lower).1 (below m)).2 lowerMember
  exact ⟨rows.trans_eq rowEqual, fun _ hz => contains
    (stageOneAssignmentUnion_contains (fun n => (seq n).assignments) n hz)⟩

end FlatSuccessorCondition
end PartitionPilot.Forcing

end

end OAI
