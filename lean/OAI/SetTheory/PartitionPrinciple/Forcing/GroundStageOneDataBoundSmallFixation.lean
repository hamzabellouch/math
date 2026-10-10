import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneGroundAction

namespace OAI

section

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
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName c.pairEmpty z}
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)
variable (collection : CollectionSchema M.sets) (t : Presentation G)
variable (inputs : StageOneActionParameters M a c.pairEmpty t b d T T2 valid)
variable (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
local notation "pairedCarrier" => M.pairEmpty_carrier_mem pairing unions powers separation c carrier
local notation "pairedOrder" => M.pairEmpty_order_mem pairing unions powers separation c carrier order
local notation "Condition" => StageOneCondition M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2
local notation "smallOrder" => M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "smallAct" => M.stageOneSmallAction a c b d T T2 valid pairing unions powers separation
  carrier order hT indices base directed system collection t inputs hT2 omega
local notation "I" => M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid
local notation "image" => M.stageOneAssignmentImage a c.pairEmpty b d T T2 valid valid2

theorem stageOneSmallAction_fixed_iff :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      (smallAct).iso g q = q ↔
      a.iso g ((equivShrink Condition).symm q).row = ((equivShrink Condition).symm q).row ∧
      image g ((equivShrink Condition).symm q).assignments = ((equivShrink Condition).symm q).assignments := by
  let := smallOrder
  intro g q
  have decoded := M.stageOneSmallAction_decode a c b d T T2 valid pairing unions powers separation
    carrier order hT indices base directed system collection t inputs hT2 omega g q
  have typed := StageOneCondition.act_eq_iff M c.pairEmpty pairing unions powers separation collection
    pairedCarrier pairedOrder hT valid a b d base directed system T2 valid2 t inputs.condition_maps
    inputs.node_maps hT2 inputs.terms_closed inputs.pairs_closed inputs.family_ground indices.index_ground
    omega g ((equivShrink Condition).symm q)
  constructor
  · intro same
    apply typed.1
    exact decoded.symm.trans (congrArg (equivShrink Condition).symm same)
  · intro fields
    apply (equivShrink Condition).symm.injective
    exact decoded.trans (typed.2 fields)

theorem stageOneSmallAction_fixed :
    letI := smallOrder
    ∀ (g : G) (q : Shrink Condition),
      a.iso g ((equivShrink Condition).symm q).row = ((equivShrink Condition).symm q).row →
      image g ((equivShrink Condition).symm q).assignments = ((equivShrink Condition).symm q).assignments →
      (smallAct).iso g q = q := by
  let := smallOrder
  intro g q row assignments
  exact (M.stageOneSmallAction_fixed_iff a c b d T T2 valid pairing unions powers separation
    carrier order hT indices base directed system collection t inputs hT2 omega g q).2 ⟨row, assignments⟩

theorem stageOneSmallAction_fixed_of_anchor_le (D : L) :
    letI := smallOrder
    ∀ (g : G) (_actor : g ∈ d.principalFix D) (q : Shrink Condition),
      a.iso g ((equivShrink Condition).symm q).row = ((equivShrink Condition).symm q).row →
      (∀ (C E : L) (U Rf Rc : (M.nameDomain c.pairEmpty).names) (u w : Name c.pairEmpty),
        refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I →
        u.val ∈ T → w.val ∈ T →
        stageOneAssignment (refinementIndexCode ∅ (b.encode C) (b.encode E)
          U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ ((equivShrink Condition).symm q).assignments →
        E ≤ D ∧ a.act c.pairEmpty g u = u ∧ a.act c.pairEmpty g w = w) →
      (smallAct).iso g q = q := by
  let := smallOrder
  intro g actor q row bounds
  apply (equivShrink Condition).symm.injective
  rw [M.stageOneSmallAction_decode a c b d T T2 valid pairing unions powers separation
    carrier order hT indices base directed system collection t inputs hT2 omega]
  exact StageOneCondition.act_fixed_of_anchor_le M c.pairEmpty pairing unions powers separation collection
    pairedCarrier pairedOrder hT valid a b d base directed system T2 valid2 t inputs.condition_maps
    inputs.node_maps hT2 inputs.terms_closed inputs.pairs_closed inputs.family_ground indices.index_ground
    omega D g actor ((equivShrink Condition).symm q) row bounds

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
variable (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets) (hT : T ∈ M.sets)
variable {valid2 : ∀ z ∈ T2, IsName c.pairEmpty z}
variable (indices : NiceRefinementIndexSystem M a c.pairEmpty b d ∅ T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a c.pairEmpty b d base directed T valid)
variable (collection : CollectionSchema M.sets) (t : Presentation G)
variable (inputs : StageOneActionParameters M a c.pairEmpty t b d T T2 valid)
variable (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
local notation "pairedCarrier" => M.pairEmpty_carrier_mem pairing unions powers separation c carrier
local notation "pairedOrder" => M.pairEmpty_order_mem pairing unions powers separation c carrier order
local notation "Condition" => StageOneCondition M c.pairEmpty pairing unions powers separation collection
  pairedCarrier pairedOrder hT valid a b d base directed system T2
local notation "smallOrder" => M.stageOneConditionSmallOrder a c b d T T2 valid pairing unions powers separation
  carrier order hT base directed system collection
local notation "smallAct" => M.stageOneSmallAction a c b d T T2 valid pairing unions powers separation
  carrier order hT indices base directed system collection t inputs hT2 omega
local notation "I" => M.niceRefinementIndices a c.pairEmpty b d ∅ T T2 valid
local notation "anchors" => refinementIndexFieldGraph I b.carrier 2

theorem stageOneSmallAction_fixed_of_dataBound (S mu X tuples : ZFSet.{u}) (D : L)
    (support : ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u) :
    letI := smallOrder
    ∀ (g : G) (_actor : g ∈ d.principalFix D) (q : Shrink Condition),
      a.iso g ((equivShrink Condition).symm q).row = ((equivShrink Condition).symm q).row →
      (∀ z ∈ ((equivShrink Condition).symm q).assignments,
        ZFSet.pair z (b.encode D) ∈ stageOneDataBounds ((equivShrink Condition).symm q).assignments
          I T S b.carrier mu X b.conditionOrder anchors tuples) →
      (smallAct).iso g q = q := by
  let := smallOrder
  intro g actor q row bound
  apply M.stageOneSmallAction_fixed_of_anchor_le a c b d T T2 valid pairing unions powers separation
    carrier order hT indices base directed system collection t inputs hT2 omega D g actor q row
  intro C E U Rf Rc u w _ _ _ member
  exact M.stageOneDataBounds_assignment_fixes a c.pairEmpty b d T T2 valid S mu X tuples
    ((equivShrink Condition).symm q).assignments D support g actor C E U Rf Rc u w (bound _ member)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
