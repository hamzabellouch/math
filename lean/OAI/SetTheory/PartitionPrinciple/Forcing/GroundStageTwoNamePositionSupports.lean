import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoActionInputs
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageTwoNameGraphs

namespace OAI

namespace PartitionPilot.Forcing

namespace CompleteProjection
universe u
variable {G P Q : Type u} [Group G] [PartialOrder P] [PartialOrder Q]
variable {restriction : Q →o P} {inclusion : P ↪o Q}

theorem inclusion_equivariant (projection : CompleteProjection restriction inclusion)
    (upper : PosetAction G Q) (lower : PosetAction G P)
    (equivariant : ∀ g q, restriction (upper.iso g q) = lower.iso g (restriction q))
    (g : G) (p : P) : upper.iso g (inclusion p) = inclusion (lower.iso g p) := by
  have forward (h : G) (q : P) : upper.iso h (inclusion q) ≤ inclusion (lower.iso h q) := by
    apply (projection.le_include_iff _ _).2
    rw [equivariant, projection.retract]
  apply le_antisymm (forward g p)
  have back := (upper.iso g).monotone (forward g⁻¹ (lower.iso g p))
  have cancel : lower.iso g⁻¹ (lower.iso g p) = p := by
    rw [← lower.mul, inv_mul_cancel, lower.one]
  rw [cancel, ← upper.mul, mul_inv_cancel, upper.one] at back
  exact back

end CompleteProjection

namespace PosetAction
open SetRealization
universe u
variable {G P Q L : Type u} [Group G] [PartialOrder P] [PartialOrder Q] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (e : PosetAction G Q) (t : Presentation Q)
variable (liftName : Name s → Name t)
variable (codes : ∀ τ, (liftName τ).val = τ.val)
variable (stabilizers : ∀ τ, e.stabilizer t (liftName τ) = a.stabilizer s τ)
include codes stabilizers

theorem positionSupport_of_codeLift (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (b : Presentation L) (d : PosetAction G L) (S mu X tuples : ZFSet.{u}) (D : L)
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ f ∈ S, ∀ τ : Name s, ZFSet.pair f τ.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s τ) :
    ∀ f ∈ S, ∀ τ : Name t, ZFSet.pair f τ.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ e.stabilizer t τ := by
  intro f hf τ entry bound
  let lower : Name s := ⟨τ.val, valid τ.val (range f τ.val entry)⟩
  have same : liftName lower = τ := Subtype.ext (codes lower)
  rw [← same, stabilizers]
  exact support f hf lower entry bound

end PosetAction

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
variable (hT : T ∈ M.sets)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)
local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "smallAct" => M.stageTwoSmallAction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs
local notation "smallRestrict" => M.stageTwoSmallRestriction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F
local notation "smallInc" => M.stageTwoSmallInclusion c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

theorem stageTwoSmallRestriction_equivariant :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      smallRestrict ((smallAct).iso g q) = a.iso g (smallRestrict q) := by
  let := smallOrder
  intro g q
  change ((equivShrink Condition).symm ((smallAct).iso g q)).lower =
    a.iso g ((equivShrink Condition).symm q).lower
  rw [M.stageTwoSmallAction_decode]
  rfl

variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)

include infinite choice hI0 hI1 in
theorem stageTwoSmallInclusion_equivariant :
    letI := smallOrder
    ∀ (g : G) (p : P),
      (smallAct).iso g (smallInc p) = smallInc (a.iso g p) := by
  let := smallOrder
  have projection := M.stageTwoSmallCompleteProjection c I0 a s b d T T2 valid
    pairing unions powers separation collection carrier order hT base directed system F first second
    infinite choice hI0 hI1
  exact projection.inclusion_equivariant smallAct a
    (M.stageTwoSmallRestriction_equivariant c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system rowAction image inputs F)

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

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "inc" => StageTwoCondition.inclusion M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

local notation "incl" => M.stageTwoSmallInclusion c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "liftName" => M.stageTwoNameLift c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system F first second
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)
local notation "smallAct" => M.stageTwoSmallAction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs

include infinite choice hI0 hI1

theorem stageTwoNameLift_act :
    letI := smallOrder
    ∀ (g : G) (τ : Name s),
      (smallAct).act (pres) g (liftName τ) = liftName (a.act s g τ) := by
  let := smallOrder
  intro g τ
  exact a.act_rename_of_equivariant (smallAct) s (pres) incl
    (fun g p => (M.stageTwoSmallInclusion_equivariant c I0 a s b d T T2 valid
      pairing unions powers separation collection carrier order hT base directed system
      rowAction image inputs F first second infinite choice hI0 hI1 g p).symm) g τ

theorem stageTwoNameLift_stabilizer :
    letI := smallOrder
    ∀ τ : Name s, (smallAct).stabilizer (pres) (liftName τ) = a.stabilizer s τ := by
  let := smallOrder
  intro τ
  apply Subgroup.ext
  intro g
  change (smallAct).act (pres) g (liftName τ) = liftName τ ↔ a.act s g τ = τ
  rw [M.stageTwoNameLift_act c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system F first second
    rowAction image inputs infinite choice hI0 hI1]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [M.stageTwoNameLift_val c I0 a s b d T T2 valid pairing unions powers separation
      collection carrier order nodes hT indices base directed system F first second] using codes
  · intro equal
    exact congrArg liftName equal

theorem stageTwoNameLift_supported (K : Subgroup G) (τ : Name s)
    (supported : K ≤ a.stabilizer s τ) :
    letI := smallOrder
    K ≤ (smallAct).stabilizer (pres) (liftName τ) := by
  let := smallOrder
  rw [M.stageTwoNameLift_stabilizer c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system F first second
    rowAction image inputs infinite choice hI0 hI1]
  exact supported

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

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))
variable (first : RefinementIndexLevelCode I0 ∅)
variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))
local notation "inc" => StageTwoCondition.inclusion M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system
local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

local notation "incl" => M.stageTwoSmallInclusion c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second
local notation "liftName" => M.stageTwoNameLift c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system F first second
variable (rowAction : PosetAction G R) (image : G → ZFSet.{u} → ZFSet.{u})
variable (inputs : StageTwoConditionActionInputs M c I0 a s b d T T2 valid pairing unions powers
  separation collection carrier order hT base directed system rowAction image)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hI0 : I0 ∈ M.sets)
variable (hI1 : M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid ∈ M.sets)
local notation "smallAct" => M.stageTwoSmallAction c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system rowAction image inputs

include F first second infinite choice hI0 hI1 in
theorem stageTwoNameLift_positionSupport (S mu X tuples : ZFSet.{u}) (D : L)
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ f ∈ S, ∀ τ : Name s, ZFSet.pair f τ.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s τ) :
    letI := smallOrder
    ∀ f ∈ S, ∀ τ : Name (pres), ZFSet.pair f τ.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ (smallAct).stabilizer (pres) τ := by
  let := smallOrder
  exact a.positionSupport_of_codeLift s (smallAct) (pres) liftName
    (M.stageTwoNameLift_val c I0 a s b d T T2 valid pairing unions powers separation
      collection carrier order nodes hT indices base directed system F first second)
    (M.stageTwoNameLift_stabilizer c I0 a s b d T T2 valid pairing unions powers separation
      collection carrier order nodes hT indices base directed system F first second
      rowAction image inputs infinite choice hI0 hI1)
    T valid b d S mu X tuples D range support

end TransitiveGround

section
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageTwoActionData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) : Prop where
  closure_data : StageTwoClosureData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection
  valid2 : ∀ z ∈ T2, IsName c.pairEmpty z
  term_graphs :
    let next := closure_data.projection_data.carrier_data.index_data.next
    ∀ g, Name.renameFamilyGraph s (e.iso g) T next.valid1 =
      Name.renameFamilyGraph c.pairEmpty (a.iso g) T valid
  term_families :
    let next := closure_data.projection_data.carrier_data.index_data.next
    e.termActionFamily s actors T next.valid1 = a.termActionFamily c.pairEmpty actors T valid
  actions :
    let prior := closure_data.projection_data.carrier_data
    let next := prior.index_data.next
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
    let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2 valid valid2 next.valid1 next.valid2
    let graph := M.stageTwoAssignmentActionGraph a c.pairEmpty e s nodes d T T2 valid valid2 next.valid1 next.valid2
    ∃ F : FlatConditionSystem M c s (stageOneAssignments I0 T),
      let Condition := StageTwoCondition M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      letI := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      ∃ hNodes : nodes.carrier ∈ M.sets,
      ∃ inputs : StageTwoConditionActionInputs M c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first a image,
        let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          hNodes prior.terms_ground next.indices base directed next.first
        let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          prior.terms_ground base directed next.first a image inputs
        let restriction := M.stageTwoSmallRestriction c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          prior.terms_ground base directed next.first F
        let inclusion := M.stageTwoSmallInclusion c I0 e s nodes d T T2 next.valid1
          pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
          prior.terms_ground base directed next.first F closure_data.projection_data.first_level next.indices.levelCode
        (∀ g A, image g A = relationImage A (stageOneAssignments (I0 ∪ I1) T) (graph g)) ∧
        familyCodeGraph actors.encode graph ∈ M.sets ∧
        action.actionGraph pres actors ∈ M.sets ∧ action.conditionMapFamily pres actors ∈ M.sets ∧
        (∀ g (q : Shrink Condition),
          ((equivShrink Condition).symm (action.iso g q)).row = a.iso g ((equivShrink Condition).symm q).row ∧
          ((equivShrink Condition).symm (action.iso g q)).assignments = image g ((equivShrink Condition).symm q).assignments ∧
          ((equivShrink Condition).symm (action.iso g q)).lower = e.iso g ((equivShrink Condition).symm q).lower) ∧
        (∀ g (q : Shrink Condition), pres.encode (action.iso g q) =
          ZFSet.pair (c.encode (a.iso g ((equivShrink Condition).symm q).row))
            (image g ((equivShrink Condition).symm q).assignments)) ∧
        (∀ g q, restriction (action.iso g q) = e.iso g (restriction q)) ∧
        (∀ g p, action.iso g (inclusion p) = inclusion (e.iso g p))

end

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
variable (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)

theorem stageTwoActionData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (prior : StageTwoClosureData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection)
    (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
    (params0 : StageOneActionParameters M a c.pairEmpty actors nodes d T T2 valid)
    (rows : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
    (hT2 : T2 ∈ M.sets)
    (hI0 : M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid ∈ M.sets)
    (nodeOrder : nodes.conditionOrder ∈ M.sets) (group : actors.carrier ∈ M.sets)
    (rowMaps : a.conditionMapFamily c actors ∈ M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (row_equivariant : ∀ (F : FlatConditionSystem M c s
      (stageOneAssignments (M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid) T)) g q,
      F.row (e.iso g q) = a.iso g (F.row q))
    (data_equivariant : ∀ (F : FlatConditionSystem M c s
      (stageOneAssignments (M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid) T)) g q,
      F.assignments (e.iso g q) = M.stageOneAssignmentImage a c.pairEmpty nodes d T T2 valid valid2 g (F.assignments q))
    (termGraphs : ∀ g,
      Name.renameFamilyGraph s (e.iso g) T prior.projection_data.carrier_data.index_data.next.valid1 =
        Name.renameFamilyGraph c.pairEmpty (a.iso g) T valid) :
    StageTwoActionData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection := by
  let data := prior.projection_data.carrier_data
  let next := data.index_data.next
  let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
  let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2 valid valid2 next.valid1 next.valid2
  let graph := M.stageTwoAssignmentActionGraph a c.pairEmpty e s nodes d T T2 valid valid2 next.valid1 next.valid2
  have carrier0 := M.pairEmpty_carrier_mem pairing unions powers separation c rows
  have order0 := M.pairEmpty_order_mem pairing unions powers separation c rows rowOrder
  have omega := M.omega_mem separation infinite
  obtain ⟨F, hNodes, _⟩ := prior.projection_data.projections
  have inputs := M.stageTwoActionInputs a c.pairEmpty c e s nodes d T T2 valid valid2 next.valid1 next.valid2
    actors pairing unions powers separation collection carrier0 order0 data.lower_carrier_ground
    data.lower_order_ground params0 next.inputs data.terms_ground hT2 hI0 next.indices.index_ground
    prior.projection_data.first_level next.indices.levelCode omega base directed next.first F
    (row_equivariant F) (data_equivariant F)
  have imageEq : ∀ g A, image g A = relationImage A
      (stageOneAssignments (I0 ∪ M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1) T) (graph g) :=
    M.stageTwoAssignmentImage_eq_relationImage a c.pairEmpty e s nodes d T T2 valid valid2 next.valid1 next.valid2
      actors pairing unions powers separation collection carrier0 order0 data.lower_carrier_ground
      data.lower_order_ground params0 next.inputs
  have familyGround : familyCodeGraph actors.encode graph ∈ M.sets :=
    M.stageTwoAssignmentActionFamily_mem_of_inputs a c.pairEmpty e s nodes d T T2 valid valid2 next.valid1 next.valid2
      actors pairing unions powers separation collection carrier0 order0 data.lower_carrier_ground
      data.lower_order_ground params0 next.inputs group hNodes data.terms_ground hT2 hI0 next.indices.index_ground omega
  refine ⟨prior, valid2, termGraphs, ?_, ?_⟩
  · unfold PosetAction.termActionFamily
    congr 1
    funext g
    exact termGraphs g
  · refine ⟨F, ?_⟩
    let := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
      data.terms_ground base directed next.first
    refine ⟨hNodes, inputs, imageEq, familyGround, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact M.stageTwoSmallActionGraph_mem c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
        hNodes data.terms_ground next.indices base directed next.first a image inputs actors graph imageEq
        rows hI0 nodeOrder omega group rowMaps familyGround
    · exact M.stageTwoSmallActionMapFamily_mem c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
        hNodes data.terms_ground next.indices base directed next.first a image inputs actors graph imageEq
        rows hI0 nodeOrder omega group rowMaps familyGround
    · intro g q
      rw [M.stageTwoSmallAction_decode]
      exact ⟨rfl, rfl, rfl⟩
    · exact M.stageTwoSmallAction_encode c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
        hNodes data.terms_ground next.indices base directed next.first a image inputs
    · exact M.stageTwoSmallRestriction_equivariant c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
        data.terms_ground base directed next.first a image inputs F
    · exact M.stageTwoSmallInclusion_equivariant c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
        data.terms_ground base directed next.first a image inputs F prior.projection_data.first_level next.indices.levelCode
        infinite choice hI0 next.indices.index_ground

end TransitiveGround

end PartitionPilot.Forcing

end OAI
