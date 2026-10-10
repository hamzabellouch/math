import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneNameLifting

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (c : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
local notation "Q" => M.stageOneForcing a c b d T T2 valid
local notation "B" => M.groundSmallSubsets
  (stageOneAssignments (M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid) T) ZFSet.omega

noncomputable def stageOneRowGraph : ZFSet.{u} := rowAssignmentRows Q c.carrier B
noncomputable def stageOneAssignmentGraph : ZFSet.{u} := rowAssignmentData Q c.carrier B

private theorem subset_product : Q ⊆ ZFSet.prod c.carrier B := by
  intro z hz
  exact ((M.mem_stageOneConditions c.carrier _ z).1 hz).1

theorem stageOneRowGraph_entry (p : P) (A x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (c.encode p) A) x ∈ M.stageOneRowGraph a c b d T T2 valid ↔
      ZFSet.pair (c.encode p) A ∈ Q ∧ x = c.encode p := by
  rw [stageOneRowGraph, rowAssignmentRows_entry]
  constructor
  · rintro ⟨member,_,_,equal⟩
    exact ⟨member,equal⟩
  · rintro ⟨member,equal⟩
    have fields := ZFSet.pair_mem_prod.1 (subset_product M a c b d T T2 valid member)
    exact ⟨member,fields.1,fields.2,equal⟩

theorem stageOneAssignmentGraph_entry (p : P) (A x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (c.encode p) A) x ∈ M.stageOneAssignmentGraph a c b d T T2 valid ↔
      ZFSet.pair (c.encode p) A ∈ Q ∧ x = A := by
  rw [stageOneAssignmentGraph, rowAssignmentData_entry]
  constructor
  · rintro ⟨member,_,_,equal⟩
    exact ⟨member,equal⟩
  · rintro ⟨member,equal⟩
    have fields := ZFSet.pair_mem_prod.1 (subset_product M a c b d T T2 valid member)
    exact ⟨member,fields.1,fields.2,equal⟩

theorem stageOneRowGraph_function : ZFSet.IsFunc Q c.carrier (M.stageOneRowGraph a c b d T T2 valid) :=
  rowAssignmentRows_function (subset_product M a c b d T T2 valid)

theorem stageOneAssignmentGraph_function : ZFSet.IsFunc Q B (M.stageOneAssignmentGraph a c b d T T2 valid) :=
  rowAssignmentData_function (subset_product M a c b d T T2 valid)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName c.pairEmpty z}
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)
include pairing unions powers separation carrier order nodes hT indices system

theorem stageOneRowGraph_mem (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.stageOneRowGraph a c b d T T2 valid ∈ M.sets := by
  have conditions := M.stageOneForcing_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system nodeOrder omega
  have assignments := M.stageOneAssignments_mem pairing unions powers separation indices.index_ground hT
  exact M.rowAssignmentRows_mem pairing unions powers separation conditions carrier
    (M.groundSmallSubsets_mem powers separation assignments omega)

theorem stageOneAssignmentGraph_mem (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.stageOneAssignmentGraph a c b d T T2 valid ∈ M.sets := by
  have conditions := M.stageOneForcing_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system nodeOrder omega
  have assignments := M.stageOneAssignments_mem pairing unions powers separation indices.index_ground hT
  exact M.rowAssignmentData_mem pairing unions powers separation conditions carrier
    (M.groundSmallSubsets_mem powers separation assignments omega)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (c : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName c.pairEmpty z}
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)
variable (collection : CollectionSchema M.sets)
local notation "pairedCarrier" => M.pairEmpty_carrier_mem pairing unions powers separation c carrier
local notation "pairedOrder" => M.pairEmpty_order_mem pairing unions powers separation c carrier order
local notation "Condition" => StageOneCondition M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2
local notation "Q" => M.stageOneForcing a c b d T T2 valid
local notation "B" => M.groundSmallSubsets
  (stageOneAssignments (M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid) T) ZFSet.omega
local notation "pres" => M.stageOneConditionPresentation a c b d T T2 valid pairing unions powers separation
  carrier order nodes hT indices base directed system collection

noncomputable def stageOneConditionRow (x : Shrink Condition) : P :=
  ((equivShrink Condition).symm x).row

noncomputable def stageOneConditionData (x : Shrink Condition) : SetMembers B :=
  SetMembers.ofMem ((equivShrink Condition).symm x).assignments
    ((equivShrink Condition).symm x).assignments_mem

local notation "row" => M.stageOneConditionRow a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "data" => M.stageOneConditionData a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection

theorem stageOneConditionData_raw (x : Shrink Condition) :
    SetMembers.raw (data x) = ((equivShrink Condition).symm x).assignments :=
  SetMembers.raw_ofMem _ _

include nodes indices in
theorem stageOneRowGraph_eq_graph :
    M.stageOneRowGraph a c b d T T2 valid = (pres).graph c row := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro member
    obtain ⟨raw,hr,x,_,rfl⟩ := ZFSet.mem_prod.1 ((M.stageOneRowGraph_function a c b d T T2 valid).1 member)
    obtain ⟨q,rfl⟩ := ((pres).mem_carrier raw).1 hr
    have value := (M.stageOneRowGraph_entry a c b d T T2 valid
      ((equivShrink Condition).symm q).row ((equivShrink Condition).symm q).assignments x).1 member
    refine ⟨q, ?_⟩
    change ZFSet.pair ((pres).encode q) (c.encode (row q)) = ZFSet.pair ((pres).encode q) x
    rw [value.2]
    rfl
  · rintro ⟨q,rfl⟩
    exact (M.stageOneRowGraph_entry a c b d T T2 valid
      ((equivShrink Condition).symm q).row ((equivShrink Condition).symm q).assignments _).2
      ⟨(pres).encode_mem q,rfl⟩

include nodes indices in
theorem stageOneAssignmentGraph_eq_graph :
    M.stageOneAssignmentGraph a c b d T T2 valid = (pres).graph (SetMembers.presentation B) data := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro member
    obtain ⟨raw,hr,x,_,rfl⟩ := ZFSet.mem_prod.1 ((M.stageOneAssignmentGraph_function a c b d T T2 valid).1 member)
    obtain ⟨q,rfl⟩ := ((pres).mem_carrier raw).1 hr
    have value := (M.stageOneAssignmentGraph_entry a c b d T T2 valid
      ((equivShrink Condition).symm q).row ((equivShrink Condition).symm q).assignments x).1 member
    refine ⟨q, ?_⟩
    change ZFSet.pair ((pres).encode q) (SetMembers.raw (data q)) = ZFSet.pair ((pres).encode q) x
    rw [M.stageOneConditionData_raw, value.2]
  · rintro ⟨q,rfl⟩
    exact (M.stageOneAssignmentGraph_entry a c b d T T2 valid
      ((equivShrink Condition).symm q).row ((equivShrink Condition).symm q).assignments _).2
      ⟨(pres).encode_mem q, M.stageOneConditionData_raw a c b d T T2 valid pairing unions powers separation
        carrier order hT base directed system collection q⟩

include nodes indices in
theorem stageOneSequence_projections_ground
    (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (seq : Nat → Shrink Condition)
    (whole : natPresentation.graph (pres) (fun n => seq n.down) ∈ M.sets) :
    natPresentation.graph c (fun n => row (seq n.down)) ∈ M.sets ∧
      groundSequenceGraph (fun n => data (seq n)) ∈ M.sets := by
  have conditions := M.stageOneForcing_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system nodeOrder omega
  have hB := M.groundSmallSubsets_mem powers separation
    (M.stageOneAssignments_mem pairing unions powers separation indices.index_ground hT) omega
  have first := M.stageOneRowGraph_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system nodeOrder omega
  have second := M.stageOneAssignmentGraph_mem a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system nodeOrder omega
  rw [M.stageOneRowGraph_eq_graph a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection] at first
  rw [M.stageOneAssignmentGraph_eq_graph a c b d T T2 valid pairing unions powers separation
    carrier order nodes hT indices base directed system collection] at second
  have rowGraph := M.relationCompose_mem pairing unions powers separation omega conditions carrier whole first
  have dataGraph := M.relationCompose_mem pairing unions powers separation omega conditions hB whole second
  have rowEqual := natPresentation.relationCompose_graph (pres) c (fun n => seq n.down) row
  have dataEqual := natPresentation.relationCompose_graph (pres) (SetMembers.presentation B) (fun n => seq n.down) data
  change relationCompose ZFSet.omega Q c.carrier
    (natPresentation.graph (pres) (fun n => seq n.down)) ((pres).graph c row) = _ at rowEqual
  change relationCompose ZFSet.omega Q B
    (natPresentation.graph (pres) (fun n => seq n.down)) ((pres).graph (SetMembers.presentation B) data) = _ at dataEqual
  rw [rowEqual] at rowGraph
  rw [dataEqual] at dataGraph
  exact ⟨rowGraph,dataGraph⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
