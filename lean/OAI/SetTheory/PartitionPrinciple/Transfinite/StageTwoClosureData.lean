import OAI.SetTheory.PartitionPrinciple.Forcing.StageTwoConditionUnions

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (c : Presentation R) (I0 : ZFSet.{u})
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
local notation "I1" => M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid
local notation "B" => M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega

noncomputable def stageTwoAssignmentGraph : ZFSet.{u} := rowAssignmentData Q c.carrier B

private theorem subset_product : Q ⊆ ZFSet.prod c.carrier B := by
  intro z hz
  exact ((M.mem_stageTwoConditions c.carrier (I0 ∪ I1) (stageTwoAssignmentLevels I0 I1 T)
    (natSetCode 1) (M.refinementLevelFormulaData a s b d (natSetCode 1) T T2 valid) z).1 hz).1

theorem stageTwoAssignmentGraph_entry (p : R) (A x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (c.encode p) A) x ∈ M.stageTwoAssignmentGraph c I0 a s b d T T2 valid ↔
      ZFSet.pair (c.encode p) A ∈ Q ∧ x = A := by
  rw [stageTwoAssignmentGraph, rowAssignmentData_entry]
  constructor
  · rintro ⟨member, _, _, equal⟩
    exact ⟨member, equal⟩
  · rintro ⟨member, equal⟩
    have fields := ZFSet.pair_mem_prod.1 (subset_product M c I0 a s b d T T2 valid member)
    exact ⟨member, fields.1, fields.2, equal⟩

theorem stageTwoAssignmentGraph_function :
    ZFSet.IsFunc Q B (M.stageTwoAssignmentGraph c I0 a s b d T T2 valid) :=
  rowAssignmentData_function (subset_product M c I0 a s b d T T2 valid)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets)
variable (hT : T ∈ M.sets) (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
include pairing unions powers separation rows hI0 hT carrier order nodes nodeOrder indices system

theorem stageTwoAssignmentGraph_mem (omega : ZFSet.omega ∈ M.sets) :
    M.stageTwoAssignmentGraph c I0 a s b d T T2 valid ∈ M.sets := by
  have conditions := M.stageTwoForcing_mem c.carrier I0 a s b d T T2 valid
    pairing unions powers separation rows hI0 hT carrier order nodes nodeOrder valid2 indices base directed system omega
  have assignments := M.stageOneAssignments_mem pairing unions powers separation
    (M.binary_union_mem pairing unions hI0 indices.index_ground) hT
  exact M.rowAssignmentData_mem pairing unions powers separation conditions rows
    (M.groundSmallSubsets_mem powers separation assignments omega)

end TransitiveGround

section
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
local notation "levels" => stageTwoAssignmentLevels I0
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T

variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)

local notation "restrict" => restriction M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F
local notation "inc" => inclusion M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

include infinite choice hI0 hI1 in
theorem completeProjection : CompleteProjection restrict inc := by
  refine ⟨?_, ?_, ?_⟩
  · exact restriction_inclusion M c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system F first second
  · exact le_inclusion_iff M c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system F first second
  · intro p q below
    obtain ⟨r, rp, lower, _, _⟩ := exists_lift_restriction M c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system F first second
      infinite choice hI0 hI1 p q below
    exact ⟨r, rp, lower⟩

end StageTwoCondition
end

namespace TransitiveGround
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
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "code" => StageTwoCondition.code M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid

local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "restrict" => StageTwoCondition.restriction M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F
local notation "inc" => StageTwoCondition.inclusion M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

noncomputable def stageTwoSmallRestriction :
    letI := smallOrder
    Shrink Condition →o P := by
  letI := smallOrder
  exact {
    toFun := fun p => restrict ((equivShrink Condition).symm p)
    monotone' := fun _ _ below => (restrict).monotone below }

noncomputable def stageTwoSmallInclusion :
    letI := smallOrder
    P ↪o Shrink Condition := by
  letI := smallOrder
  exact {
    toFun := fun p => equivShrink Condition (inc p)
    inj' := fun _ _ equal => (inc).injective ((equivShrink Condition).injective equal)
    map_rel_iff' := by
      intro p q
      change (equivShrink Condition).symm (equivShrink Condition (inc p)) ≤
        (equivShrink Condition).symm (equivShrink Condition (inc q)) ↔ p ≤ q
      simp only [Equiv.symm_apply_apply]
      exact (inc).map_rel_iff }

local notation "smallRestrict" => M.stageTwoSmallRestriction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F
local notation "smallInc" => M.stageTwoSmallInclusion c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)

include infinite choice hI0 hI1 in
theorem stageTwoSmallCompleteProjection :
    letI := smallOrder
    CompleteProjection smallRestrict smallInc := by
  let := smallOrder
  have original := StageTwoCondition.completeProjection M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system F first second
    infinite choice hI0 hI1
  refine ⟨?_, ?_, ?_⟩
  · intro q
    change restrict ((equivShrink Condition).symm (equivShrink Condition (inc q))) = q
    rw [Equiv.symm_apply_apply]
    exact original.retract q
  · intro p q
    change (equivShrink Condition).symm p ≤
      (equivShrink Condition).symm (equivShrink Condition (inc q)) ↔
      restrict ((equivShrink Condition).symm p) ≤ q
    rw [Equiv.symm_apply_apply]
    exact original.le_include_iff _ q
  · intro p q below
    obtain ⟨r, rp, lower⟩ := original.lift ((equivShrink Condition).symm p) q below
    refine ⟨equivShrink Condition r, ?_, ?_⟩
    · change (equivShrink Condition).symm (equivShrink Condition r) ≤ (equivShrink Condition).symm p
      rw [Equiv.symm_apply_apply]
      exact rp
    · change restrict ((equivShrink Condition).symm (equivShrink Condition r)) = q
      rw [Equiv.symm_apply_apply]
      exact lower

theorem stageTwoSmallInclusion_encode :
    letI := smallOrder
    ∀ q : P, (pres).encode (smallInc q) = s.encode q := by
  let := smallOrder
  intro q
  change (pres).encode (equivShrink Condition (inc q)) = s.encode q
  rw [M.stageTwoConditionPresentation_encode]
  exact StageTwoCondition.includeLower_code M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system F first second q

theorem stageTwoSmallRestriction_encode :
    letI := smallOrder
    ∀ p : Shrink Condition, s.encode (smallRestrict p) =
      ZFSet.pair (c.encode ((equivShrink Condition).symm p).row)
        (assignmentCut (stageTwoAssignmentLevels I0
          (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T)
          (natSetCode 1) ((equivShrink Condition).symm p).assignments) := by
  let := smallOrder
  intro p
  exact ((equivShrink Condition).symm p).lower_code

end TransitiveGround

namespace TransitiveGround
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
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "code" => StageTwoCondition.code M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid

local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
local notation "smallRestrict" => M.stageTwoSmallRestriction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F
local notation "levels" => stageTwoAssignmentLevels I0
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) T

theorem stageTwoSmallRestriction_graph :
    letI := smallOrder
    (pres).graph s smallRestrict = rowAssignmentCutGraph Q s.carrier levels (natSetCode 1) := by
  let := smallOrder
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · rintro ⟨p, rfl⟩
    let decoded := (equivShrink Condition).symm p
    change ZFSet.pair (ZFSet.pair (c.encode decoded.row) decoded.assignments)
      (s.encode (smallRestrict p)) ∈ _
    exact (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2
      ⟨(pres).encode_mem p, s.encode_mem (smallRestrict p),
        M.stageTwoSmallRestriction_encode c I0 a s b d T T2 valid pairing unions powers separation
          collection carrier order hT base directed system F p⟩
  · intro member
    obtain ⟨upper, hu, lower, _, equal⟩ := ZFSet.mem_prod.1
      ((mem_rowAssignmentCutGraph _ _ _ _ z).1 member).1
    obtain ⟨p, ep⟩ := ((pres).mem_carrier upper).1 hu
    have entry : ZFSet.pair ((pres).encode p) lower ∈
        rowAssignmentCutGraph Q s.carrier levels (natSetCode 1) := by
      rw [ep, ← equal]
      exact member
    let decoded := (equivShrink Condition).symm p
    change ZFSet.pair (ZFSet.pair (c.encode decoded.row) decoded.assignments) lower ∈ _ at entry
    have parts := (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).1 entry
    have lowerEqual : s.encode (smallRestrict p) = lower :=
      (M.stageTwoSmallRestriction_encode c I0 a s b d T T2 valid pairing unions powers separation
        collection carrier order hT base directed system F p).trans parts.2.2.symm
    refine ⟨p, ?_⟩
    change ZFSet.pair ((pres).encode p) (s.encode (smallRestrict p)) = z
    rw [ep, lowerEqual]
    exact equal.symm

theorem stageTwoSmallRestriction_graph_mem
    (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    letI := smallOrder
    (pres).graph s smallRestrict ∈ M.sets := by
  let := smallOrder
  rw [M.stageTwoSmallRestriction_graph c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system F]
  exact M.rowAssignmentCutGraph_mem pairing unions powers separation
    (M.stageTwoForcing_mem c.carrier I0 a s b d T T2 valid pairing unions powers separation
      rows hI0 hT carrier order nodes nodeOrder valid2 indices base directed system omega)
    carrier (M.stageTwoAssignmentLevels_mem pairing unions powers separation hI0 indices.index_ground hT)
    (M.transitive omega (natSetCode_mem_omega 1))

end TransitiveGround

namespace TransitiveGround
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
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "I1" => M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid
local notation "B" => M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

noncomputable def stageTwoConditionData (x : Shrink Condition) : SetMembers B :=
  SetMembers.ofMem ((equivShrink Condition).symm x).assignments
    ((equivShrink Condition).symm x).assignments_mem

local notation "data" => M.stageTwoConditionData c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

omit [PartialOrder R] in
theorem stageTwoConditionData_raw (x : Shrink Condition) :
    SetMembers.raw (data x) = ((equivShrink Condition).symm x).assignments :=
  SetMembers.raw_ofMem _ _

include nodes indices in
omit [PartialOrder R] in
theorem stageTwoAssignmentGraph_eq_graph :
    M.stageTwoAssignmentGraph c I0 a s b d T T2 valid = (pres).graph (SetMembers.presentation B) data := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro member
    obtain ⟨raw, hr, x, _, rfl⟩ := ZFSet.mem_prod.1
      ((M.stageTwoAssignmentGraph_function c I0 a s b d T T2 valid).1 member)
    obtain ⟨q, rfl⟩ := ((pres).mem_carrier raw).1 hr
    have value := (M.stageTwoAssignmentGraph_entry c I0 a s b d T T2 valid
      ((equivShrink Condition).symm q).row ((equivShrink Condition).symm q).assignments x).1 member
    refine ⟨q, ?_⟩
    change ZFSet.pair ((pres).encode q) (SetMembers.raw (data q)) = ZFSet.pair ((pres).encode q) x
    rw [M.stageTwoConditionData_raw, value.2]
  · rintro ⟨q, rfl⟩
    exact (M.stageTwoAssignmentGraph_entry c I0 a s b d T T2 valid
      ((equivShrink Condition).symm q).row ((equivShrink Condition).symm q).assignments _).2
      ⟨(pres).encode_mem q, M.stageTwoConditionData_raw c I0 a s b d T T2 valid
        pairing unions powers separation collection carrier order hT base directed system q⟩

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
local notation "restrict" => M.stageTwoSmallRestriction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F

include nodes indices in
theorem stageTwoSequence_projections_ground
    (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (seq : Nat → Shrink Condition)
    (whole : natPresentation.graph (pres) (fun n => seq n.down) ∈ M.sets) :
    letI := smallOrder
    natPresentation.graph s (fun n => (restrict) (seq n.down)) ∈ M.sets ∧
      groundSequenceGraph (fun n => data (seq n)) ∈ M.sets := by
  let := smallOrder
  have conditions := M.stageTwoForcing_mem c.carrier I0 a s b d T T2 valid
    pairing unions powers separation rows hI0 hT carrier order nodes nodeOrder valid2 indices base directed system omega
  have assignments := M.stageOneAssignments_mem pairing unions powers separation
    (M.binary_union_mem pairing unions hI0 indices.index_ground) hT
  have hB := M.groundSmallSubsets_mem powers separation assignments omega
  have first := M.stageTwoSmallRestriction_graph_mem c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system F
    rows hI0 nodeOrder omega
  have second := M.stageTwoAssignmentGraph_mem c I0 a s b d T T2 valid
    pairing unions powers separation rows hI0 hT carrier order nodes nodeOrder indices base directed system omega
  rw [M.stageTwoAssignmentGraph_eq_graph c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system] at second
  have lowerGraph := M.relationCompose_mem pairing unions powers separation omega conditions carrier whole first
  have dataGraph := M.relationCompose_mem pairing unions powers separation omega conditions hB whole second
  have lowerEqual := natPresentation.relationCompose_graph (pres) s (fun n => seq n.down) (restrict)
  have dataEqual := natPresentation.relationCompose_graph (pres) (SetMembers.presentation B)
    (fun n => seq n.down) data
  change relationCompose ZFSet.omega Q s.carrier
    (natPresentation.graph (pres) (fun n => seq n.down)) ((pres).graph s (restrict)) = _ at lowerEqual
  change relationCompose ZFSet.omega Q B
    (natPresentation.graph (pres) (fun n => seq n.down)) ((pres).graph (SetMembers.presentation B) data) = _ at dataEqual
  rw [lowerEqual] at lowerGraph
  rw [dataEqual] at dataGraph
  exact ⟨lowerGraph, dataGraph⟩

end TransitiveGround

section
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageTwoProjectionData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) : Prop where
  carrier_data : StageTwoCarrierData M c.carrier (c.encode ⊤) a c.pairEmpty e s actors nodes d
    base directed T T2 valid pairing unions powers separation collection
  first_level : RefinementIndexLevelCode (M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid) ∅
  projections :
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let next := carrier_data.index_data.next
    let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
    let hT := carrier_data.terms_ground
    let hP := carrier_data.lower_carrier_ground
    let hOrder := carrier_data.lower_order_ground
    ∃ F : FlatConditionSystem M c s (stageOneAssignments I0 T),
      let Condition := StageTwoCondition M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection hP hOrder hT base directed next.first
      letI := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection hP hOrder hT base directed next.first
      letI := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection hP hOrder hT base directed next.first
        F first_level next.indices.levelCode
      ∃ hNodes : nodes.carrier ∈ M.sets,
        let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection hP hOrder hNodes hT next.indices base directed next.first
        let restriction := M.stageTwoSmallRestriction c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection hP hOrder hT base directed next.first F
        let inclusion := M.stageTwoSmallInclusion c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection hP hOrder hT base directed next.first
          F first_level next.indices.levelCode
        pres.carrier = M.stageTwoForcing c.carrier I0 e s nodes d T T2 next.valid1 ∧
        pres.carrier ∈ M.sets ∧
        pres.conditionOrder = rowAssignmentOrder pres.carrier c.carrier
          (M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega) c.conditionOrder ∧
        pres.conditionOrder ∈ M.sets ∧ pres.encode ⊤ = s.encode ⊤ ∧
        CompleteProjection restriction inclusion ∧
        (∀ q : P, pres.encode (inclusion q) = s.encode q) ∧
        (∀ p : Shrink Condition, s.encode (restriction p) =
          ZFSet.pair (c.encode ((equivShrink Condition).symm p).row)
            (assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1)
              ((equivShrink Condition).symm p).assignments)) ∧
        pres.graph s restriction = rowAssignmentCutGraph pres.carrier s.carrier
          (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) ∧
        pres.graph s restriction ∈ M.sets

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
variable (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)

theorem stageTwoProjectionData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (prior : StageTwoCarrierData M c.carrier (c.encode ⊤) a c.pairEmpty e s actors nodes d
      base directed T T2 valid pairing unions powers separation collection)
    (F : FlatConditionSystem M c s
      (stageOneAssignments (M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid) T))
    (first : RefinementIndexLevelCode (M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid) ∅)
    (rows : c.carrier ∈ M.sets)
    (hI0 : M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid ∈ M.sets)
    (rowOrder : c.conditionOrder ∈ M.sets) (hNodes : nodes.carrier ∈ M.sets)
    (nodeOrder : nodes.conditionOrder ∈ M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    StageTwoProjectionData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection := by
  let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
  let next := prior.index_data.next
  let hT := prior.terms_ground
  let hP := prior.lower_carrier_ground
  let hOrder := prior.lower_order_ground
  refine ⟨prior, first, F, ?_⟩
  let := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection hP hOrder hT base directed next.first
  let := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection hP hOrder hT base directed next.first F first next.indices.levelCode
  refine ⟨hNodes, rfl, prior.carrier_ground, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (M.stageTwoFlatConditionSystem c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection hP hOrder hNodes hT next.indices
      base directed next.first).conditionOrder_eq
  · exact M.stageTwoConditionOrder_mem c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection hP hOrder hNodes hT next.indices base directed next.first
      rows hI0 rowOrder nodeOrder (M.omega_mem separation infinite)
  · exact M.stageTwoConditionPresentation_top c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection hP hOrder hNodes hT next.indices base directed next.first
      F first next.indices.levelCode
  · exact M.stageTwoSmallCompleteProjection c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection hP hOrder hT base directed next.first
      F first next.indices.levelCode infinite choice hI0 next.indices.index_ground
  · exact M.stageTwoSmallInclusion_encode c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection hP hOrder hNodes hT next.indices base directed next.first
      F first next.indices.levelCode
  · exact M.stageTwoSmallRestriction_encode c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection hP hOrder hT base directed next.first F
  · exact M.stageTwoSmallRestriction_graph c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection hP hOrder hNodes hT next.indices base directed next.first F
  · exact M.stageTwoSmallRestriction_graph_mem c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection hP hOrder hNodes hT next.indices base directed next.first F
      rows hI0 nodeOrder (M.omega_mem separation infinite)

end TransitiveGround
end

namespace TransitiveGround
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
variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid

local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "restrict" => StageTwoCondition.restriction M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F
local notation "smallRestrict" => M.stageTwoSmallRestriction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F
local notation "data" => M.stageTwoConditionData c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "I1" => M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid
local notation "B" => M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega
local notation "levels" => stageTwoAssignmentLevels I0 I1 T
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (rows : c.carrier ∈ M.sets) (hI0 : I0 ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets)
variable (closed : InternallyCountablyClosed M s)

include F first second infinite choice rows hI0 nodeOrder closed in
theorem stageTwoCondition_lower_bound :
    letI := smallOrder
    ∀ seq : Nat → Shrink Condition,
      natPresentation.graph (pres) (fun n => seq n.down) ∈ M.sets → Antitone seq →
      ∃ q : P, (∀ n, q ≤ smallRestrict (seq n)) ∧ ∃ p : Shrink Condition,
        ((equivShrink Condition).symm p).lower = q ∧
        ((equivShrink Condition).symm p).assignments =
          assignmentSplice levels (natSetCode 1) (F.assignments q)
            (stageOneAssignmentUnion (fun n => ((equivShrink Condition).symm (seq n)).assignments)) ∧
        ∀ n, p ≤ seq n := by
  let := smallOrder
  intro seq whole decreasing
  let typed : Nat → Condition := fun n => (equivShrink Condition).symm (seq n)
  have typedDecreasing : Antitone typed := fun _ _ less => decreasing less
  have lowerDecreasing : Antitone (fun n => smallRestrict (seq n)) :=
    fun _ _ less => (smallRestrict).monotone (decreasing less)
  obtain ⟨lowerGround, dataGround⟩ := M.stageTwoSequence_projections_ground c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    F rows hI0 nodeOrder (M.omega_mem separation infinite) seq whole
  obtain ⟨q, below⟩ := closed (fun n => smallRestrict (seq n)) lowerGround lowerDecreasing
  have hJ := M.stageOneAssignments_mem pairing unions powers separation
    (M.binary_union_mem pairing unions hI0 indices.index_ground) hT
  have smallRaw := M.groundSmallSubset_union_mem pairing unions powers separation infinite choice
    hJ (fun n => data (seq n)) dataGround
  have small : stageOneAssignmentUnion (fun n => (typed n).assignments) ∈ B := by
    simpa only [M.stageTwoConditionData_raw] using smallRaw
  let lower : Condition := StageTwoCondition.chainUnion M c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system
    F first second infinite choice hI0 indices.index_ground typed typedDecreasing q below small
  refine ⟨q, below, equivShrink Condition lower, ?_, ?_, ?_⟩
  · rw [Equiv.symm_apply_apply]
    rfl
  · rw [Equiv.symm_apply_apply]
    rfl
  · intro n
    change (equivShrink Condition).symm (equivShrink Condition lower) ≤ typed n
    rw [Equiv.symm_apply_apply]
    exact StageTwoCondition.chainUnion_le M c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system
      F first second infinite choice hI0 indices.index_ground typed typedDecreasing q below small n

include F first second infinite choice rows hI0 nodeOrder closed in
theorem stageTwoCondition_internally_closed :
    letI := smallOrder
    InternallyCountablyClosed M (pres) := by
  let := smallOrder
  intro seq whole decreasing
  obtain ⟨_, _, q, _, _, below⟩ := M.stageTwoCondition_lower_bound c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order nodes hT indices base directed system
    F first second infinite choice rows hI0 nodeOrder closed seq whole decreasing
  exact ⟨q, below⟩

end TransitiveGround

open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageTwoClosureData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) : Prop where
  projection_data : StageTwoProjectionData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection
  closed :
    let prior := projection_data.carrier_data
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let next := prior.index_data.next
    letI := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
      prior.terms_ground base directed next.first
    ∃ hNodes : nodes.carrier ∈ M.sets,
      InternallyCountablyClosed M
        (M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          hNodes prior.terms_ground next.indices base directed next.first)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
variable (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)

theorem stageTwoClosureData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (prior : StageTwoProjectionData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection)
    (rows : c.carrier ∈ M.sets)
    (hI0 : M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid ∈ M.sets)
    (nodeOrder : nodes.conditionOrder ∈ M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (lowerClosed : InternallyCountablyClosed M s) :
    StageTwoClosureData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection := by
  let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
  let data := prior.carrier_data
  let next := data.index_data.next
  obtain ⟨F, hNodes, _⟩ := prior.projections
  refine ⟨prior, hNodes, ?_⟩
  exact M.stageTwoCondition_internally_closed c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
    hNodes data.terms_ground next.indices base directed next.first F prior.first_level next.indices.levelCode
    infinite choice rows hI0 nodeOrder lowerClosed

end TransitiveGround

end PartitionPilot.Forcing

end OAI
