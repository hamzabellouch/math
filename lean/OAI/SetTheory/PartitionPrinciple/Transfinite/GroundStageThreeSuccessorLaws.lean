import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatRestrictionGraphs
import OAI.SetTheory.PartitionPrinciple.Geometry.RefinementLevelThreeTestGuards

namespace OAI

namespace PartitionPilot.Forcing

section
universe u
variable {P : Type u} [PartialOrder P]

structure FlatSuccessorLaws (Jold I T levels alpha : ZFSet.{u})
    (tests : ZFSet.{u} → P → Prop) : Prop where
  old_subset : Jold ⊆ stageOneAssignments I T
  cut_subset : ∀ A, A ⊆ stageOneAssignments I T → assignmentCut levels alpha A ⊆ Jold
  cut_old : ∀ A, A ⊆ Jold → assignmentCut levels alpha A = A
  tests_mono : ∀ {A p q}, tests A p → q ≤ p → tests A q
  tests_splice : ∀ Aq Ap p, Aq ⊆ Jold →
    (tests (assignmentSplice levels alpha Aq Ap) p ↔ tests Ap p)
  tests_old : ∀ A p, A ⊆ Jold → tests A p

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R P : Type u} [PartialOrder R]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests

namespace FlatSuccessorCondition
instance partialOrder : PartialOrder Condition where
  le p q := p.row ≤ q.row ∧ q.assignments ⊆ p.assignments
  le_refl _ := ⟨le_rfl, fun _ h => h⟩
  le_trans _ _ _ first second := ⟨first.1.trans second.1, fun _ h => first.2 (second.2 h)⟩
  le_antisymm p q first second := by
    apply ext M c s I T levels alpha tests (le_antisymm first.1 second.1)
    apply ZFSet.ext
    intro z
    exact ⟨fun h => second.2 h, fun h => first.2 h⟩

theorem le_iff (p q : Condition) :
    p ≤ q ↔ p.row ≤ q.row ∧ q.assignments ⊆ p.assignments := Iff.rfl

def rowProjection : Condition →o R where
  toFun p := p.row
  monotone' _ _ below := below.1

end FlatSuccessorCondition

namespace TransitiveGround
@[instance_reducible]
noncomputable def flatSuccessorSmallOrder : PartialOrder (Shrink Condition) where
  le p q := (equivShrink Condition).symm p ≤ (equivShrink Condition).symm q
  le_refl _ := le_rfl
  le_trans _ _ _ first second := first.trans second
  le_antisymm _ _ first second := (equivShrink Condition).symm.injective (le_antisymm first second)

local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "pres" => M.flatSuccessorPresentation c s I T levels alpha tests

noncomputable def flatSuccessorOrderIso :
    letI := smallOrder
    Condition ≃o Shrink Condition := by
  let := smallOrder
  exact {
    toEquiv := equivShrink Condition
    map_rel_iff' := by
      intro p q
      change (equivShrink Condition).symm (equivShrink Condition p) ≤
        (equivShrink Condition).symm (equivShrink Condition q) ↔ p ≤ q
      simp only [Equiv.symm_apply_apply] }

noncomputable def flatSuccessorFlatConditionSystem :
    letI := smallOrder
    FlatConditionSystem M c pres (stageOneAssignments I T) := by
  let := smallOrder
  exact {
    row := fun p => ((equivShrink Condition).symm p).row
    assignments := fun p => ((equivShrink Condition).symm p).assignments
    encode := fun _ => rfl
    le_iff := fun _ _ => Iff.rfl
    assignments_mem := fun p => ((equivShrink Condition).symm p).assignments_mem }

theorem flatSuccessorConditionOrder_eq :
    letI := smallOrder
    (pres).conditionOrder = rowAssignmentOrder (pres).carrier c.carrier
      (M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega) c.conditionOrder := by
  let := smallOrder
  exact (M.flatSuccessorFlatConditionSystem c s I T levels alpha tests).conditionOrder_eq

theorem flatSuccessorConditionOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (rows : c.carrier ∈ M.sets)
    (conditions : M.flatSuccessorCarrier c s I T levels alpha tests ∈ M.sets)
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (order : c.conditionOrder ∈ M.sets) :
    letI := smallOrder
    (pres).conditionOrder ∈ M.sets := by
  let := smallOrder
  exact (M.flatSuccessorFlatConditionSystem c s I T levels alpha tests).conditionOrder_mem
    pairing unions powers separation rows conditions
    (M.stageOneAssignments_mem pairing unions powers separation hI hT) omega order

end TransitiveGround
end

section
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)

namespace FlatSuccessorCondition
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
variable {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)

theorem lower_row (p : Condition) : F.row p.lower = p.row :=
  c.injective (ZFSet.pair_inj.1 ((F.encode p.lower).symm.trans p.lower_code)).1

theorem lower_assignments (p : Condition) :
    F.assignments p.lower = assignmentCut levels alpha p.assignments :=
  (ZFSet.pair_inj.1 ((F.encode p.lower).symm.trans p.lower_code)).2

def restriction : Condition →o P where
  toFun p := p.lower
  monotone' := by
    intro p q below
    apply (F.le_iff p.lower q.lower).2
    constructor
    · rw [lower_row M c s I T levels alpha tests F p,
        lower_row M c s I T levels alpha tests F q]
      exact below.1
    · rw [lower_assignments M c s I T levels alpha tests F p,
        lower_assignments M c s I T levels alpha tests F q]
      exact assignmentCut_mono below.2

variable (laws : FlatSuccessorLaws Jold I T levels alpha tests)

noncomputable def includeLower (q : P) : Condition := by
  have facts := (M.mem_groundSmallSubsets Jold ZFSet.omega _).1 (F.assignments_mem q)
  have ground := facts.1
  have subsetOld := facts.2.1
  have small := facts.2.2
  refine ⟨F.row q, F.assignments q, ?_, q, ?_, ?_⟩
  · exact (M.mem_groundSmallSubsets _ _ _).2
      ⟨ground, fun _ hz => laws.old_subset (subsetOld hz), small⟩
  · rw [laws.cut_old _ subsetOld]
    exact F.encode q
  · exact laws.tests_old _ q subsetOld

local notation "inc" => includeLower M c s I T levels alpha tests F laws
local notation "restrict" => restriction M c s I T levels alpha tests F

theorem includeLower_lower (q : P) : (inc q).lower = q := rfl

theorem includeLower_code (q : P) :
    code M c s I T levels alpha tests (inc q) = s.encode q := (F.encode q).symm

noncomputable def inclusion : P ↪o Condition where
  toFun := inc
  inj' _ _ equal := congrArg FlatSuccessorCondition.lower equal
  map_rel_iff' := by
    intro p q
    exact (F.le_iff p q).symm

theorem restriction_inclusion (q : P) :
    restrict (inclusion M c s I T levels alpha tests F laws q) = q := rfl

theorem le_inclusion_iff (p : Condition) (q : P) :
    p ≤ inclusion M c s I T levels alpha tests F laws q ↔ restrict p ≤ q := by
  change p.row ≤ F.row q ∧ F.assignments q ⊆ p.assignments ↔ p.lower ≤ q
  rw [F.le_iff, lower_row M c s I T levels alpha tests F p,
    lower_assignments M c s I T levels alpha tests F p]
  apply and_congr_right
  intro _
  have subsetOld := ((M.mem_groundSmallSubsets _ _ (F.assignments q)).1
    (F.assignments_mem q)).2.1
  constructor
  · intro subset
    have mono : assignmentCut levels alpha (F.assignments q) ⊆
        assignmentCut levels alpha p.assignments := assignmentCut_mono subset
    rwa [laws.cut_old _ subsetOld] at mono
  · intro subset
    exact fun _ hz => assignmentCut_subset _ _ _ (subset hz)

end FlatSuccessorCondition
end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)

namespace FlatSuccessorCondition
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
variable {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)
variable (laws : FlatSuccessorLaws Jold I T levels alpha tests)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)

noncomputable def splice (p : Condition) (q : P) (below : q ≤ p.lower) : Condition := by
  have old := ((M.mem_groundSmallSubsets _ _ _).1 (F.assignments_mem q)).2.1
  have memberq : F.assignments q ∈ M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega :=
    (includeLower M c s I T levels alpha tests F laws q).assignments_mem
  exact {
    row := F.row q
    assignments := assignmentSplice levels alpha (F.assignments q) p.assignments
    assignments_mem := M.assignmentSplice_mem_groundSmallSubsets pairing unions powers separation
      infinite choice hLevels hAlpha memberq p.assignments_mem
    lower := q
    lower_code := by rw [assignmentCut_splice, laws.cut_old _ old]; exact F.encode q
    tests := (laws.tests_splice _ _ q old).2 (laws.tests_mono p.tests below) }

local notation "lifted" => splice M c s I T levels alpha tests F laws
  pairing unions powers separation infinite choice hLevels hAlpha

theorem splice_row (p : Condition) (q : P) (below : q ≤ p.lower) :
    (lifted p q below).row = F.row q := rfl

theorem splice_assignments (p : Condition) (q : P) (below : q ≤ p.lower) :
    (lifted p q below).assignments =
      assignmentSplice levels alpha (F.assignments q) p.assignments := rfl

theorem splice_lower (p : Condition) (q : P) (below : q ≤ p.lower) :
    (lifted p q below).lower = q := rfl

theorem splice_le (p : Condition) (q : P) (below : q ≤ p.lower) : lifted p q below ≤ p := by
  obtain ⟨rows, data⟩ := (F.le_iff q p.lower).1 below
  have lowerRow := lower_row M c s I T levels alpha tests F p
  have lowerData := lower_assignments M c s I T levels alpha tests F p
  refine ⟨rows.trans_eq lowerRow, ?_⟩
  change p.assignments ⊆ assignmentSplice levels alpha (F.assignments q) p.assignments
  apply assignmentSplice_extends
  rw [laws.cut_old _ ((M.mem_groundSmallSubsets _ _ _).1 (F.assignments_mem q)).2.1,
    ← lowerData]
  exact data

include laws pairing unions powers separation infinite choice hLevels hAlpha in
theorem exists_lift_restriction (p : Condition) (q : P) (below : q ≤ p.lower) :
    ∃ r : Condition, r ≤ p ∧ r.lower = q ∧ r.row = F.row q ∧
      r.assignments = assignmentSplice levels alpha (F.assignments q) p.assignments :=
  ⟨lifted p q below, splice_le M c s I T levels alpha tests F laws
    pairing unions powers separation infinite choice hLevels hAlpha p q below, rfl, rfl, rfl⟩

include laws pairing unions powers separation infinite choice hLevels hAlpha in
theorem completeProjection :
    CompleteProjection (restriction M c s I T levels alpha tests F)
      (inclusion M c s I T levels alpha tests F laws) := by
  refine ⟨restriction_inclusion M c s I T levels alpha tests F laws,
    le_inclusion_iff M c s I T levels alpha tests F laws, ?_⟩
  intro p q below
  obtain ⟨r, rp, lower, _, _⟩ := exists_lift_restriction M c s I T levels alpha tests F laws
    pairing unions powers separation infinite choice hLevels hAlpha p q below
  exact ⟨r, rp, lower⟩

end FlatSuccessorCondition
end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "pres" => M.flatSuccessorPresentation c s I T levels alpha tests
variable {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)
variable (laws : FlatSuccessorLaws Jold I T levels alpha tests)
local notation "restrict" => FlatSuccessorCondition.restriction M c s I T levels alpha tests F
local notation "inc" => FlatSuccessorCondition.inclusion M c s I T levels alpha tests F laws

noncomputable def flatSuccessorSmallRestriction :
    letI := smallOrder
    Shrink Condition →o P := by
  let := smallOrder
  exact {
    toFun := fun p => restrict ((equivShrink Condition).symm p)
    monotone' := fun _ _ below => (restrict).monotone below }

noncomputable def flatSuccessorSmallInclusion :
    letI := smallOrder
    P ↪o Shrink Condition := by
  let := smallOrder
  exact {
    toFun := fun p => equivShrink Condition (inc p)
    inj' := fun _ _ equal => (inc).injective ((equivShrink Condition).injective equal)
    map_rel_iff' := by
      intro p q
      change (equivShrink Condition).symm (equivShrink Condition (inc p)) ≤
        (equivShrink Condition).symm (equivShrink Condition (inc q)) ↔ p ≤ q
      simp only [Equiv.symm_apply_apply]
      exact (inc).map_rel_iff }

local notation "smallRestrict" => M.flatSuccessorSmallRestriction c s I T levels alpha tests F
local notation "smallInc" => M.flatSuccessorSmallInclusion c s I T levels alpha tests F laws

include laws in
theorem flatSuccessorSmallCompleteProjection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) :
    letI := smallOrder
    CompleteProjection smallRestrict smallInc := by
  let := smallOrder
  have original := FlatSuccessorCondition.completeProjection M c s I T levels alpha tests F laws
    pairing unions powers separation infinite choice hLevels hAlpha
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

theorem flatSuccessorSmallInclusion_encode :
    letI := smallOrder
    ∀ q : P, (pres).encode (smallInc q) = s.encode q := by
  let := smallOrder
  intro q
  change (pres).encode (equivShrink Condition (inc q)) = s.encode q
  rw [M.flatSuccessorPresentation_encode]
  exact FlatSuccessorCondition.includeLower_code M c s I T levels alpha tests F laws q

theorem flatSuccessorSmallRestriction_encode :
    letI := smallOrder
    ∀ p : Shrink Condition, s.encode (smallRestrict p) =
      ZFSet.pair (c.encode ((equivShrink Condition).symm p).row)
        (assignmentCut levels alpha ((equivShrink Condition).symm p).assignments) := by
  let := smallOrder
  intro p
  exact ((equivShrink Condition).symm p).lower_code

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable [PartialOrder R] [PartialOrder P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "Q" => M.flatSuccessorCarrier c s I T levels alpha tests
local notation "B" => M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega
local notation "pres" => M.flatSuccessorPresentation c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "data" => M.flatSuccessorConditionData c s I T levels alpha tests
variable {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)
local notation "restrict" => M.flatSuccessorSmallRestriction c s I T levels alpha tests F

theorem flatSuccessorSequence_projections_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (rows : c.carrier ∈ M.sets) (conditions : Q ∈ M.sets) (lower : s.carrier ∈ M.sets)
    (assignments : stageOneAssignments I T ∈ M.sets)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (seq : Nat → Shrink Condition)
    (whole : natPresentation.graph (pres) (fun n => seq n.down) ∈ M.sets) :
    letI := smallOrder
    natPresentation.graph s (fun n => restrict (seq n.down)) ∈ M.sets ∧
      groundSequenceGraph (fun n => data (seq n)) ∈ M.sets := by
  let := smallOrder
  have hB := M.groundSmallSubsets_mem powers separation assignments omega
  have first := M.presentedRowAssignmentCutGraph_mem pairing unions powers separation
    pres s restrict (fun p => c.encode ((equivShrink Condition).symm p).row)
    (fun p => ((equivShrink Condition).symm p).assignments) levels alpha
    (fun _ => rfl) (M.flatSuccessorSmallRestriction_encode c s I T levels alpha tests F)
    conditions lower hLevels hAlpha
  have second := M.flatSuccessorAssignmentGraph_mem c s I T levels alpha tests
    pairing unions powers separation conditions rows assignments omega
  rw [M.flatSuccessorAssignmentGraph_eq_graph c s I T levels alpha tests] at second
  have lowerGraph := M.relationCompose_mem pairing unions powers separation omega conditions lower whole first
  have dataGraph := M.relationCompose_mem pairing unions powers separation omega conditions hB whole second
  have lowerEqual := natPresentation.relationCompose_graph pres s (fun n => seq n.down) restrict
  have dataEqual := natPresentation.relationCompose_graph pres (SetMembers.presentation B)
    (fun n => seq n.down) data
  change relationCompose ZFSet.omega Q s.carrier
    (natPresentation.graph pres (fun n => seq n.down)) ((pres).graph s restrict) = _ at lowerEqual
  change relationCompose ZFSet.omega Q B
    (natPresentation.graph pres (fun n => seq n.down)) ((pres).graph (SetMembers.presentation B) data) = _ at dataEqual
  rw [lowerEqual] at lowerGraph
  rw [dataEqual] at dataGraph
  exact ⟨lowerGraph, dataGraph⟩

end TransitiveGround

namespace TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R P : Type u}
variable [PartialOrder R] [PartialOrder P] [OrderTop P]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests
local notation "pres" => M.flatSuccessorPresentation c s I T levels alpha tests
variable {Jold : ZFSet.{u}} (F : FlatConditionSystem M c s Jold)
variable (laws : FlatSuccessorLaws Jold I T levels alpha tests)
local notation "inc" => FlatSuccessorCondition.inclusion M c s I T levels alpha tests F laws

@[instance_reducible]
noncomputable def flatSuccessorConditionTop : OrderTop Condition where
  top := inc ⊤
  le_top p := (FlatSuccessorCondition.le_inclusion_iff M c s I T levels alpha tests F laws p ⊤).2 le_top

@[instance_reducible]
noncomputable def flatSuccessorSmallTop :
    letI := smallOrder
    OrderTop (Shrink Condition) := by
  let := smallOrder
  exact {
    top := equivShrink Condition (inc ⊤)
    le_top := by
      intro p
      change (equivShrink Condition).symm p ≤
        (equivShrink Condition).symm (equivShrink Condition (inc ⊤))
      rw [Equiv.symm_apply_apply]
      exact (FlatSuccessorCondition.le_inclusion_iff M c s I T levels alpha tests F laws _ ⊤).2 le_top }

theorem flatSuccessorPresentation_top :
    letI := smallOrder
    letI := M.flatSuccessorSmallTop c s I T levels alpha tests F laws
    (pres).encode ⊤ = s.encode ⊤ := by
  let := smallOrder
  let := M.flatSuccessorSmallTop c s I T levels alpha tests F laws
  change (pres).encode (equivShrink Condition (inc ⊤)) = s.encode ⊤
  rw [M.flatSuccessorPresentation_encode]
  exact FlatSuccessorCondition.includeLower_code M c s I T levels alpha tests F laws ⊤

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable {I0 I1 T2 : ZFSet.{u}}
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode I1 (natSetCode 1))
variable (third : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid) (natSetCode 2))
include first second third

theorem stageThreeFlatSuccessorLaws :
    let I2 := M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid
    FlatSuccessorLaws (stageOneAssignments (I0 ∪ I1) T) ((I0 ∪ I1) ∪ I2) T
      (stageThreeAssignmentLevels I0 I1 I2 T) (natSetCode 2)
      (M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system (natSetCode 2) T2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stageOneAssignments_union (I0 ∪ I1)
      (M.niceRefinementIndices a s b d (natSetCode 2) T T2 valid) T]
    exact fun _ hz => ZFSet.mem_union.2 (Or.inl hz)
  · intro A _ z hz
    rw [stageThreeAssignmentCut_two first second third] at hz
    exact (ZFSet.mem_sep.1 hz).2
  · intro A subset
    exact stageThreeAssignmentCut_two_eq first second third subset
  · intro A p q tests below
    exact M.refinementLevelTests_mono s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (natSetCode 2) T2 A tests below
  · intro Aq Ap p _
    exact M.refinementLevelTests_stageThreeSplice s pairing unions powers separation collection
      carrier order hT valid a b d base directed system first second third Aq Ap p
  · intro A p subset
    exact M.refinementLevelTests_stageThreeOld s pairing unions powers separation collection
      carrier order hT valid a b d base directed system first second third p subset

end TransitiveGround

end PartitionPilot.Forcing

end OAI
