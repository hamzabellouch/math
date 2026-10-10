import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalStageThreeAction

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder P] [PartialOrder L]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
variable (b : Presentation L) (d : PosetAction G L)
local notation "Condition" => FlatSuccessorCondition M c s I T levels alpha tests
local notation "smallOrder" => M.flatSuccessorSmallOrder c s I T levels alpha tests

structure FlatSuccessorPositionSupport (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u})
    (action : letI := smallOrder; PosetAction G (Shrink Condition)) : Prop where
  bounds : letI := smallOrder
    ∀ (q : Shrink Condition) (extra : ZFSet.{u}),
      extra ∈ M.sets → extra ⊆ b.carrier → M.groundEmbeddable extra ZFSet.omega →
      ∃ D : L,
        (∀ x : L, b.encode x ∈ used ((equivShrink Condition).symm q).row → x ≤ D) ∧
        (∀ z ∈ ((equivShrink Condition).symm q).assignments,
          ZFSet.pair z (b.encode D) ∈ stageOneDataBounds ((equivShrink Condition).symm q).assignments
            I T S b.carrier mu X b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples) ∧
        (∀ x : L, b.encode x ∈ extra → x ≤ D) ∧
        (∀ g ∈ d.principalFix D, action.iso g q = q)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G P Q : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable [PartialOrder P] [OrderTop P] [PartialOrder Q] [OrderTop Q]
variable (e1 : PosetAction G P) (t1 : Presentation P)
variable (e2 : PosetAction G Q) (t2 : Presentation Q)
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include order choice countable_bound

theorem binaryRowStageThreePositionSupport {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
    ∀ (hLifted : lifted ∈ M.sets)
      (valid0 : ∀ z ∈ lifted, IsName c.pairEmpty z) (valid02 : ∀ z ∈ squared, IsName c.pairEmpty z)
      (valid1 : ∀ z ∈ lifted, IsName t1 z) (valid12 : ∀ z ∈ squared, IsName t1 z)
      (valid2 : ∀ z ∈ lifted, IsName t2 z) (valid22 : ∀ z ∈ squared, IsName t2 z)
      (_indices0 : NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid0 valid02)
      (_indices1 : NiceRefinementIndexSystem M e1 t1 s a (natSetCode 1) lifted squared valid1 valid12)
      (_indices2 : NiceRefinementIndexSystem M e2 t2 s a (natSetCode 2) lifted squared valid2 valid22)
      (_params0 : StageOneActionParameters M act c.pairEmpty b s a lifted squared valid0)
      (_params1 : StageOneActionParameters M e1 t1 b s a lifted squared valid1)
      (_params2 : StageOneActionParameters M e2 t2 b s a lifted squared valid2)
      (system2 : NiceNameSystem M e2 t2 s a ⊥ directed lifted valid2)
      (_carrier1 : t1.carrier ∈ M.sets) (_order1 : t1.conditionOrder ∈ M.sets)
      (carrier2 : t2.carrier ∈ M.sets) (order2 : t2.conditionOrder ∈ M.sets),
    let I0 := M.niceRefinementIndices act c.pairEmpty s a ∅ lifted squared valid0
    let I1 := M.niceRefinementIndices e1 t1 s a (natSetCode 1) lifted squared valid1
    let I2 := M.niceRefinementIndices e2 t2 s a (natSetCode 2) lifted squared valid2
    let levels := stageThreeAssignmentLevels I0 I1 I2 lifted
    let tests := M.refinementLevelTests t2 pairing unions powers separation collection carrier2 order2 hLifted
      valid2 e2 s a ⊥ directed system2 (natSetCode 2) squared
    let image := M.stageThreeAssignmentImage act c.pairEmpty e1 t1 e2 t2 s a lifted squared
      valid0 valid02 valid1 valid12 valid2 valid22
    ∀ inputs : FlatSuccessorActionInputs M c t2 ((I0 ∪ I1) ∪ I2) lifted levels (natSetCode 2) tests act e2 image,
      (∀ (D : L), ∀ f ∈ S, ∀ u : Name t1, ZFSet.pair f u.val ∈ tuples →
        RowPositionBound mu s.nonbottom.carrier s.conditionOrder f (s.encode D) →
        a.principalFix D ≤ e1.stabilizer t1 u) →
      (∀ (D : L), ∀ f ∈ S, ∀ u : Name t2, ZFSet.pair f u.val ∈ tuples →
        RowPositionBound mu s.nonbottom.carrier s.conditionOrder f (s.encode D) →
        a.principalFix D ≤ e2.stabilizer t2 u) →
      FlatSuccessorPositionSupport M c t2 ((I0 ∪ I1) ∪ I2) lifted levels (natSetCode 2) tests s a
        S mu s.nonbottom.carrier tuples
        (fun p => rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p))
        (M.flatSuccessorSmallAction c t2 ((I0 ∪ I1) ∪ I2) lifted levels (natSetCode 2) tests act e2 image inputs) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted valid0 valid02 valid1 valid12 valid2 valid22
    indices0 indices1 indices2 params0 params1 params2 system2 carrier1 order1 carrier2 order2
    I0 I1 I2 levels tests image inputs support1 support2
  let := M.flatSuccessorSmallOrder c t2 ((I0 ∪ I1) ∪ I2) lifted levels (natSetCode 2) tests
  refine ⟨?_⟩
  intro q extra hExtra extraSubset extraSmall
  let p := (equivShrink _).symm q
  obtain ⟨D, rowBound, dataBound, extraBound⟩ :=
    M.binaryRowStageThreeDataBound s C e1 t1 e2 t2 a pairing unions powers separation collection infinite choice
      hL order hC directed countable_bound hmu ⊤ valid hLifted act squared
      valid0 valid02 valid1 valid12 valid2 valid22 indices0 indices1 indices2
      p.row p.assignments p.assignments_mem extra hExtra extraSubset extraSmall
  refine ⟨D, rowBound, dataBound, extraBound, ?_⟩
  intro g actor
  apply (M.flatSuccessorSmallAction_fixed_iff c t2 ((I0 ∪ I1) ∪ I2) lifted levels (natSetCode 2) tests
    act e2 image inputs g q).2
  constructor
  · exact M.internalRowAction_eq_of_principalFix a s b C pairing unions powers separation infinite
      hL hC hG graph g p.row D (fun i used => rowBound i.val used) actor
  · have coordinates := M.prod_mem pairing unions powers separation
      (M.nonbottom_carrier_mem s separation hL) hC
    have two := M.natSetCode_mem separation infinite 2
    have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    exact M.stageThreeAssignmentImage_eq_of_dataBound act c.pairEmpty e1 t1 e2 t2 s a lifted squared
      valid0 valid02 valid1 valid12 valid2 valid22 b pairing unions powers separation collection
      (M.pairEmpty_carrier_mem pairing unions powers separation c carrier)
      (M.pairEmpty_order_mem pairing unions powers separation c carrier forcingOrder)
      carrier1 order1 carrier2 order2 params0 params1 params2
      indices0.levelCode indices1.levelCode indices2.levelCode
      S mu s.nonbottom.carrier tuples D
      (fun f _ u entry bound => M.liftedRowTuple_supported a s b C pairing unions powers separation
        infinite hL hC hG graph hmu ordinal valid f u D entry bound.2)
      (support1 D) (support2 D) g actor
      ((M.mem_groundSmallSubsets (stageOneAssignments ((I0 ∪ I1) ∪ I2) lifted) ZFSet.omega _).1
        p.assignments_mem).2.1 dataBound

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageThreeSupportData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u}) : Prop where
  action_data : StageThreeActionData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection S mu X tuples used
  support :
    let actionData := action_data.closure_data.projection_data.carrier_data.name_lifting.support_data.action_data
    let prior := actionData.closure_data.projection_data.carrier_data
    let next := prior.index_data.next
    let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
    let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
      valid actionData.valid2 next.valid1 next.valid2
    ∃ F : FlatConditionSystem M c s (stageOneAssignments I0 T),
      letI := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first
      letI := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1
        pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
        prior.terms_ground base directed next.first F actionData.closure_data.projection_data.first_level
        next.indices.levelCode
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
        ∃ next2 : RefinementStageSystem M action pres actors nodes d base directed (natSetCode 2) T T2,
          let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
          let I2 := M.niceRefinementIndices action pres nodes d (natSetCode 2) T T2 next2.valid1
          let levels := stageThreeAssignmentLevels I0 I1 I2 T
          ∃ hCarrier : pres.carrier ∈ M.sets, ∃ hOrder : pres.conditionOrder ∈ M.sets,
          let tests := M.refinementLevelTests pres pairing unions powers separation collection
            hCarrier hOrder prior.terms_ground next2.valid1
            action nodes d base directed next2.first (natSetCode 2) T2
          let image3 := M.stageThreeAssignmentImage a c.pairEmpty e s action pres nodes d T T2
            valid actionData.valid2 next.valid1 next.valid2 next2.valid1 next2.valid2
          ∃ inputs3 : FlatSuccessorActionInputs M c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
            a action image3,
            letI := M.flatSuccessorSmallOrder c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
            TransitiveGround.FlatSuccessorPositionSupport M c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
              nodes d S mu X tuples used
              (M.flatSuccessorSmallAction c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
                a action image3 inputs3)

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable [PartialOrder P] [OrderTop P]
variable (e1 : PosetAction G P) (t1 : Presentation P)
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include order choice countable_bound

theorem binaryRowStageThreeSupportData {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
    ∀ (_hLifted : lifted ∈ M.sets)
      (valid0 : ∀ z ∈ lifted, IsName c.pairEmpty z) (valid02 : ∀ z ∈ squared, IsName c.pairEmpty z)
      (_indices0 : NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid0 valid02)
      (_params0 : StageOneActionParameters M act c.pairEmpty b s a lifted squared valid0)
      (_prior : StageThreeActionData M act c e1 t1 b s a ⊥ directed lifted squared valid0
        pairing unions powers separation collection S mu s.nonbottom.carrier tuples
        (fun p => rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p))),
      StageThreeSupportData M act c e1 t1 b s a ⊥ directed lifted squared valid0
        pairing unions powers separation collection S mu s.nonbottom.carrier tuples
        (fun p => rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p)) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted valid0 valid02 indices0 params0 priorAction
  refine ⟨priorAction, ?_⟩
  let actionData := priorAction.closure_data.projection_data.carrier_data.name_lifting.support_data.action_data
  let prior := actionData.closure_data.projection_data.carrier_data
  let next := prior.index_data.next
  let I0 := M.niceRefinementIndices act c.pairEmpty s a ∅ lifted squared valid0
  let image := M.stageTwoAssignmentImage act c.pairEmpty e1 t1 s a lifted squared
    valid0 actionData.valid2 next.valid1 next.valid2
  let firstLevel := actionData.closure_data.projection_data.first_level
  let secondLevel := next.indices.levelCode
  let := M.stageTwoConditionSmallOrder c I0 e1 t1 s a lifted squared next.valid1
    pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
    prior.terms_ground ⊥ directed next.first
  obtain ⟨F, hNodes, inputs2, next2, hCarrier, hOrder, inputs3, _⟩ := priorAction.actions
  refine ⟨F, hNodes, inputs2, next2, hCarrier, hOrder, inputs3, ?_⟩
  let := M.stageTwoConditionSmallTop c I0 e1 t1 s a lifted squared next.valid1
    pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
    prior.terms_ground ⊥ directed next.first F firstLevel secondLevel
  let pres2 := M.stageTwoConditionPresentation c I0 e1 t1 s a lifted squared next.valid1
    pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
    hNodes prior.terms_ground next.indices ⊥ directed next.first
  let action2 := M.stageTwoSmallAction c I0 e1 t1 s a lifted squared next.valid1
    pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
    prior.terms_ground ⊥ directed next.first act image inputs2
  have tupleRange : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ lifted := by
    intro f z entry
    exact ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1
  have support1 : ∀ (D : L), ∀ f ∈ S, ∀ u : Name t1,
      ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu s.nonbottom.carrier s.conditionOrder f (s.encode D) →
      a.principalFix D ≤ e1.stabilizer t1 u := by
    intro D
    apply act.positionSupport_of_term_graphs c.pairEmpty e1 t1 lifted valid0 next.valid1
      actionData.term_graphs s a S mu s.nonbottom.carrier tuples D tupleRange
    intro f _ u entry bound
    exact M.liftedRowTuple_supported a s b C pairing unions powers separation infinite
      hL hC hG graph hmu ordinal valid f u D entry bound.2
  have support2 : ∀ (D : L), ∀ f ∈ S, ∀ u : Name pres2,
      ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu s.nonbottom.carrier s.conditionOrder f (s.encode D) →
      a.principalFix D ≤ action2.stabilizer pres2 u := by
    intro D
    exact M.stageTwoNameLift_positionSupport c I0 e1 t1 s a lifted squared next.valid1
      pairing unions powers separation collection prior.lower_carrier_ground prior.lower_order_ground
      hNodes prior.terms_ground next.indices ⊥ directed next.first F firstLevel secondLevel
      act image inputs2 infinite choice indices0.index_ground next.indices.index_ground
      S mu s.nonbottom.carrier tuples D tupleRange (support1 D)
  have result := M.binaryRowStageThreePositionSupport e1 t1 action2 pres2 a s b C
    pairing unions powers separation collection infinite choice hL order hC hG graph directed
    countable_bound hmu ordinal valid hLifted valid0 actionData.valid2 next.valid1 next.valid2
    next2.valid1 next2.valid2 indices0 next.indices next2.indices params0 next.inputs next2.inputs next2.first
    prior.lower_carrier_ground prior.lower_order_ground hCarrier hOrder inputs3 support1 support2
  exact result

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

theorem exists_rowStageThreeSupport
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, geometry.carrier_ground⟩
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let hCoordinates := M.prod_mem pairing unions powers separation
      (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
    let hTwo := M.natSetCode_mem separation infinite 2
    let hRow := M.countablePartialFunctions_mem pairing unions powers separation infinite hCoordinates hTwo
    let hOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite hCoordinates hTwo
    let directed := geometry.decoded_directed fulfilled.directed
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
      T ∈ M.sets ∧ GroundBelow M T K ∧ ∃ valid : ∀ z ∈ T, IsName c z,
        let lifted := Name.renamedFamily c.pairEmpty id T valid
        let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
        let graph := Name.renameFamilyGraph c.pairEmpty id T valid
        (∃ hLifted : lifted ∈ M.sets, ∃ hSquared : squared ∈ M.sets, graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          ∃ valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z,
          ∃ valid2 : ∀ z ∈ squared, IsName c.pairEmpty z,
            ∃ first : NiceNameSystem M act c.pairEmpty s a ⊥ directed lifted valid1,
            NiceNameSystem M act c.pairEmpty s a ⊥ directed squared valid2 ∧
            ∃ indexSystem : NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid1 valid2,
            ∃ inputs : StageOneActionParameters M act c.pairEmpty b s a lifted squared valid1,
            act.conditionMapFamily c b ∈ M.sets ∧
            M.stageOneForcing act c s a lifted squared valid1 ∈ M.sets ∧
            M.stageOneForcingOrder act c s a lifted squared valid1 ∈ M.sets ∧
            (letI := M.stageOneConditionSmallOrder act c s a lifted squared valid1
              pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
             ∃ nextAction,
              nextAction = M.stageOneSmallAction act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder hLifted indexSystem ⊥ directed first
                collection b inputs hSquared (M.omega_mem separation infinite) ∧
              TransitiveGround.StageOneSmallActionLaws M act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                indexSystem ⊥ directed first collection nextAction ∧
              nextAction.actionGraph
                (M.stageOneConditionPresentation act c s a lifted squared valid1
                  pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                  indexSystem ⊥ directed first collection) b ∈ M.sets ∧
              nextAction.conditionMapFamily
                (M.stageOneConditionPresentation act c s a lifted squared valid1
                  pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                  indexSystem ⊥ directed first collection) b ∈ M.sets ∧
              InternallyCountablyClosed M
              (M.stageOneConditionPresentation act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                indexSystem ⊥ directed first collection) ∧
              TransitiveGround.StageOnePositionSupport M act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
                S mu s.nonbottom.carrier
                (liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid)
                (fun p => rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p))
                nextAction ∧
              (letI := M.stageOneConditionSmallTop act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
               let nextPres := M.stageOneConditionPresentation act c s a lifted squared valid1
                 pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                 indexSystem ⊥ directed first collection
               StageThreeSupportData M act c nextAction nextPres b s a ⊥ directed
                 lifted squared valid1 pairing unions powers separation collection
                 S mu s.nonbottom.carrier
                 (liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid)
                 (fun p => rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p)))) ∧
            (∀ C E (U Rf Rc : (M.nameDomain c.pairEmpty).names),
              refinementIndexCode ∅ (s.encode C) (s.encode E) U.val.val Rf.val.val Rc.val.val ∈
                M.niceRefinementIndices act c.pairEmpty s a ∅ lifted squared valid1 →
              RefinementObjectSystem M act c.pairEmpty (a.principalSupportFamily ⊥ directed)
                (a.principalFix C) lifted valid1 U.val Rf.val Rc.val) ∧
            ∀ n : Nat, Name.renamedFamily c.pairEmpty id (iteratedPairNameFamily (c.encode ⊤) T n)
                (iteratedPairNameFamily_valid ⊤ valid n) =
              iteratedPairNameFamily (c.pairEmpty.encode ⊤) lifted n) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  have original := fulfilled.exists_rowStageThreeAction collection infinite choice hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, data⟩ := data
  refine data.elim (fun valid data => ?_)
  refine data.elim (fun liftedGround data => ?_)
  refine data.elim (fun squaredGround data => ?_)
  obtain ⟨graphGround, injection, data⟩ := data
  refine data.elim (fun valid1 data => ?_)
  refine data.elim (fun valid2 data => ?_)
  refine data.elim (fun first data => ?_)
  obtain ⟨second, data⟩ := data
  refine data.elim (fun indexSystem data => ?_)
  refine data.elim (fun inputs data => ?_)
  obtain ⟨originalMaps, forcingGround, orderGround, actionData, objects, finitePowers⟩ := data
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    liftedGround, squaredGround, graphGround, injection, valid1, valid2,
    first, second, indexSystem, inputs, originalMaps,
    forcingGround, orderGround, ?_, objects, finitePowers⟩
  let lifted := Name.renamedFamily c.pairEmpty id _ valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let := M.stageOneConditionSmallOrder act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder liftedGround ⊥ directed first collection
  obtain ⟨nextAction, equal, laws, wholeAction, wholeMaps, closed, support, priorAction⟩ := actionData
  refine ⟨nextAction, equal, laws, wholeAction, wholeMaps, closed, support, ?_⟩
  let := M.stageOneConditionSmallTop act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder liftedGround ⊥ directed first collection
  let nextPres := M.stageOneConditionPresentation act c s a lifted squared valid1
    pairing unions powers separation carrier forcingOrder geometry.carrier_ground liftedGround
    indexSystem ⊥ directed first collection
  have countableBound := geometry.decoded_countable_bound
    (fun W hW subset small => (fulfilled.countable_localization W hW subset small).2)
  exact M.binaryRowStageThreeSupportData nextAction nextPres a s b columns
    pairing unions powers separation collection infinite choice geometry.carrier_ground order
    hColumns geometry.actors_ground action directed countableBound hmu cardinal.1 valid
    liftedGround valid1 valid2 indexSystem inputs priorAction

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
