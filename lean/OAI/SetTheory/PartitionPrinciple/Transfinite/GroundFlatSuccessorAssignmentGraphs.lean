import OAI.SetTheory.PartitionPrinciple.Forcing.FlatSuccessorConditions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRowAssignmentProjections

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "code" => FlatSuccessorCondition.code M c s I T levels alpha tests

noncomputable def flatSuccessorCarrier : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p : Condition, code p = z) (M.stageOneCandidateBound c.carrier I T)

theorem mem_flatSuccessorCarrier (z : ZFSet.{u}) :
    z ∈ M.flatSuccessorCarrier c s I T levels alpha tests ↔ ∃ p : Condition, code p = z := by
  rw [flatSuccessorCarrier, ZFSet.mem_sep]
  exact ⟨And.right, fun ⟨p, equal⟩ =>
    ⟨equal ▸ FlatSuccessorCondition.code_mem_candidateBound M c s I T levels alpha tests p,
      p, equal⟩⟩

theorem flatSuccessorCarrier_subset :
    M.flatSuccessorCarrier c s I T levels alpha tests ⊆ M.stageOneCandidateBound c.carrier I T :=
  fun _ member => (ZFSet.mem_sep.1 member).1

theorem pair_mem_flatSuccessorCarrier (row A : ZFSet.{u}) :
    ZFSet.pair row A ∈ M.flatSuccessorCarrier c s I T levels alpha tests ↔
      row ∈ c.carrier ∧ A ∈ M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega ∧
      ∃ lower : P, s.encode lower = ZFSet.pair row (assignmentCut levels alpha A) ∧
        tests A lower := by
  rw [M.mem_flatSuccessorCarrier]
  constructor
  · rintro ⟨p, equal⟩
    change ZFSet.pair (c.encode p.row) p.assignments = ZFSet.pair row A at equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨c.encode_mem p.row, p.assignments_mem, p.lower, p.lower_code, p.tests⟩
  · rintro ⟨rowMem, small, lower, lowerCode, test⟩
    obtain ⟨r, rfl⟩ := (c.mem_carrier row).1 rowMem
    exact ⟨⟨r, A, small, lower, lowerCode, test⟩, rfl⟩

theorem flatSuccessorCode_mem (p : Condition) :
    code p ∈ M.flatSuccessorCarrier c s I T levels alpha tests :=
  (M.mem_flatSuccessorCarrier c s I T levels alpha tests _).2 ⟨p, rfl⟩

noncomputable def flatSuccessorPresentation : Presentation (Shrink Condition) where
  carrier := M.flatSuccessorCarrier c s I T levels alpha tests
  encode x := code ((equivShrink Condition).symm x)
  injective := (FlatSuccessorCondition.code_injective M c s I T levels alpha tests).comp
    (equivShrink Condition).symm.injective
  mem_carrier z := by
    rw [M.mem_flatSuccessorCarrier]
    constructor
    · rintro ⟨p, equal⟩
      exact ⟨equivShrink Condition p, by simpa only [Equiv.symm_apply_apply] using equal⟩
    · rintro ⟨x, equal⟩
      exact ⟨(equivShrink Condition).symm x, equal⟩

theorem flatSuccessorPresentation_encode (p : Condition) :
    (M.flatSuccessorPresentation c s I T levels alpha tests).encode (equivShrink Condition p) =
      code p := congrArg code ((equivShrink Condition).symm_apply_apply p)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "Q" => M.flatSuccessorCarrier c s I T levels alpha tests
local notation "B" => M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega
local notation "pres" => M.flatSuccessorPresentation c s I T levels alpha tests

noncomputable def flatSuccessorAssignmentGraph : ZFSet.{u} := rowAssignmentData Q c.carrier B

theorem flatSuccessorAssignmentGraph_entry (row A x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair row A) x ∈ M.flatSuccessorAssignmentGraph c s I T levels alpha tests ↔
      ZFSet.pair row A ∈ Q ∧ x = A := by
  rw [flatSuccessorAssignmentGraph, rowAssignmentData_entry]
  constructor
  · rintro ⟨member, _, _, equal⟩
    exact ⟨member, equal⟩
  · rintro ⟨member, equal⟩
    have fields := ZFSet.pair_mem_prod.1
      (M.flatSuccessorCarrier_subset c s I T levels alpha tests member)
    exact ⟨member, fields.1, fields.2, equal⟩

theorem flatSuccessorAssignmentGraph_function :
    ZFSet.IsFunc Q B (M.flatSuccessorAssignmentGraph c s I T levels alpha tests) :=
  rowAssignmentData_function (M.flatSuccessorCarrier_subset c s I T levels alpha tests)

noncomputable def flatSuccessorConditionData (q : Shrink Condition) : SetMembers B :=
  SetMembers.ofMem ((equivShrink Condition).symm q).assignments
    ((equivShrink Condition).symm q).assignments_mem

local notation "data" => M.flatSuccessorConditionData c s I T levels alpha tests

theorem flatSuccessorConditionData_raw (q : Shrink Condition) :
    SetMembers.raw (data q) = ((equivShrink Condition).symm q).assignments :=
  SetMembers.raw_ofMem _ _

theorem flatSuccessorAssignmentGraph_eq_graph :
    M.flatSuccessorAssignmentGraph c s I T levels alpha tests =
      (pres).graph (SetMembers.presentation B) data := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro member
    obtain ⟨raw, hr, x, _, rfl⟩ := ZFSet.mem_prod.1
      ((M.flatSuccessorAssignmentGraph_function c s I T levels alpha tests).1 member)
    obtain ⟨q, rfl⟩ := ((pres).mem_carrier raw).1 hr
    have value := (M.flatSuccessorAssignmentGraph_entry c s I T levels alpha tests
      (c.encode ((equivShrink Condition).symm q).row)
      ((equivShrink Condition).symm q).assignments x).1 member
    refine ⟨q, ?_⟩
    change ZFSet.pair ((pres).encode q) (SetMembers.raw (data q)) = ZFSet.pair ((pres).encode q) x
    rw [M.flatSuccessorConditionData_raw, value.2]
  · rintro ⟨q, rfl⟩
    exact (M.flatSuccessorAssignmentGraph_entry c s I T levels alpha tests
      (c.encode ((equivShrink Condition).symm q).row)
      ((equivShrink Condition).symm q).assignments _).2
      ⟨(pres).encode_mem q, M.flatSuccessorConditionData_raw c s I T levels alpha tests q⟩

theorem flatSuccessorAssignmentGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (conditions : Q ∈ M.sets) (rows : c.carrier ∈ M.sets)
    (assignments : stageOneAssignments I T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.flatSuccessorAssignmentGraph c s I T levels alpha tests ∈ M.sets :=
  M.rowAssignmentData_mem pairing unions powers separation conditions rows
    (M.groundSmallSubsets_mem powers separation assignments omega)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
