import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalStageThreeNameLifting

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem finiteFlatHistoryCoherence (values : Nat → ZFSet.{u}) (n : Nat) (levels : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hStages : natSetCode n ∈ M.sets) (hHistory : finiteStageHistory values n ∈ M.sets)
    (hLevels : levels ∈ M.sets)
    (flat : ∀ i < n, ∀ z ∈ values i, ∃ row A, z = ZFSet.pair row A)
    (self : ∀ i < n, ∀ row A, ZFSet.pair row A ∈ values i →
      assignmentCut levels (natSetCode i) A = A)
    (adjacent : ∀ i, i + 1 < n → ∀ row A, ZFSet.pair row A ∈ values (i + 1) →
      ZFSet.pair row (assignmentCut levels (natSetCode i) A) ∈ values i) :
    FiniteFlatHistoryCoherence M values n levels := by
  have down := finiteFlatCuts_down values n levels self adjacent
  refine ⟨hStages, hHistory, hLevels, flat, down,
    M.rowAssignmentTransitionFamily_mem pairing unions powers separation hStages hHistory hLevels,
    M.rowAssignmentTransitionFamily_function pairing unions powers separation hStages hHistory hLevels
      (finiteStageHistory_function values n), ?_, ?_, ?_, ?_⟩
  · intro i hi j hj R
    exact M.rowAssignmentTransitionFamily_entry pairing unions powers separation hStages hHistory hLevels
      (finiteStageHistory_function values n)
      ((pair_mem_finiteStageHistory values n i (values i)).2 ⟨hi, rfl⟩)
      ((pair_mem_finiteStageHistory values n j (values j)).2 ⟨hj, rfl⟩)
  · intro i hi j below
    exact rowAssignmentCutGraph_function (values i) (values j) levels (natSetCode j)
      (flat i hi) (down i hi j below)
  · intro i hi
    exact rowAssignmentCutGraph_identity (values i) levels (natSetCode i) (flat i hi) (self i hi)
  · intro i hi j hji k hkj
    have subset : (natSetCode k : ZFSet.{u}) ⊆ natSetCode j := by
      intro z hz
      obtain ⟨m, hm, rfl⟩ := (mem_natSetCode z k).1 hz
      exact (natSetCode_mem_iff m j).2 (Nat.lt_of_lt_of_le hm hkj)
    exact rowAssignmentCutGraph_nested (values i) (values j) (values k) levels
      (natSetCode k) (natSetCode j) subset (down i hi j hji)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageThreeHistoryData (M : TransitiveGround.{u})
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u}) : Prop where
  name_lifting : StageThreeNameLiftingData M a c e s actors nodes d base directed T T2 valid
    pairing unions powers separation collection S mu X tuples used
  history :
    let actionData := name_lifting.support_data.action_data.closure_data.projection_data.carrier_data.name_lifting.support_data.action_data
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
          let pres3 := M.flatSuccessorPresentation c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
          let values := fourFlatStageValues c.pairEmpty.carrier s.carrier pres.carrier pres3.carrier
          let carrierHistory := finiteStageHistory values 4
          let indexHistory := threeRefinementHistory I0 I1 I2
          carrierHistory ∈ M.sets ∧ FunctionGraphOn (natSetCode 4) carrierHistory ∧
          indexHistory ∈ M.sets ∧ FunctionGraphOn (natSetCode 3) indexHistory ∧
          refinementHistoryIndices (natSetCode 3) indexHistory = (I0 ∪ I1) ∪ I2 ∧
          refinementHistoryAssignmentLevels (natSetCode 3) indexHistory T = levels ∧
          FiniteFlatHistoryCoherence M values 4 levels ∧
          M.flatLimitConditions c.carrier ((I0 ∪ I1) ∪ I2) T (natSetCode 4) carrierHistory levels =
            pres3.carrier

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable {G R P L : Type u} [Group G]
variable [PartialOrder R] [OrderTop R] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (M : TransitiveGround.{u})
theorem stageThreeHistoryData
    (a : PosetAction G R) (c : Presentation R) (e : PosetAction G P) (s : Presentation P)
    (actors : Presentation G) (nodes : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName c.pairEmpty z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (S mu X tuples : ZFSet.{u}) (used : R → ZFSet.{u})
    (prior : StageThreeNameLiftingData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used)
    (rows : c.carrier ∈ M.sets)
    (hI0 : M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid ∈ M.sets)
    (nodeOrder : nodes.conditionOrder ∈ M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) :
    StageThreeHistoryData M a c e s actors nodes d base directed T T2 valid
      pairing unions powers separation collection S mu X tuples used := by
  let actionData := prior.support_data.action_data.closure_data.projection_data.carrier_data.name_lifting.support_data.action_data
  let data := actionData.closure_data.projection_data.carrier_data
  let next := data.index_data.next
  let I0 := M.niceRefinementIndices a c.pairEmpty nodes d ∅ T T2 valid
  let I1 := M.niceRefinementIndices e s nodes d (natSetCode 1) T T2 next.valid1
  let image := M.stageTwoAssignmentImage a c.pairEmpty e s nodes d T T2
    valid actionData.valid2 next.valid1 next.valid2
  let first := actionData.closure_data.projection_data.first_level
  let second := next.indices.levelCode
  let stageTwoOrder := M.stageTwoConditionSmallOrder c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first
  obtain ⟨F, hNodes, inputs, next2, hCarrier, hOrder, _, _⟩ := prior.lifting
  let stageTwoTop := M.stageTwoConditionSmallTop c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first F first second
  let pres := M.stageTwoConditionPresentation c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground hNodes data.terms_ground next.indices base directed next.first
  let action := M.stageTwoSmallAction c I0 e s nodes d T T2 next.valid1 pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground data.terms_ground base directed next.first a image inputs
  let I2 := M.niceRefinementIndices action pres nodes d (natSetCode 2) T T2 next2.valid1
  let levels := stageThreeAssignmentLevels I0 I1 I2 T
  let tests := M.refinementLevelTests pres pairing unions powers separation collection hCarrier hOrder
    data.terms_ground next2.valid1 action nodes d base directed next2.first (natSetCode 2) T2
  let F2 := M.stageTwoFlatConditionSystem c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
    hNodes data.terms_ground next.indices base directed next.first
  let successorOrder := M.flatSuccessorSmallOrder c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
  let pres3 := M.flatSuccessorPresentation c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
  let F3 := M.flatSuccessorFlatConditionSystem c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests
  let r21 := M.stageTwoSmallRestriction c I0 e s nodes d T T2 next.valid1
    pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
    data.terms_ground base directed next.first F
  let r32 := M.flatSuccessorSmallRestriction c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2
  have code21 : ∀ p, s.encode (r21 p) = ZFSet.pair (c.encode (F2.row p))
      (assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) (F2.assignments p)) :=
    M.stageTwoSmallRestriction_encode c I0 e s nodes d T T2 next.valid1
      pairing unions powers separation collection data.lower_carrier_ground data.lower_order_ground
      data.terms_ground base directed next.first F
  have code32 : ∀ p, pres.encode (r32 p) = ZFSet.pair (c.encode (F3.row p))
      (assignmentCut levels (natSetCode 2) (F3.assignments p)) :=
    M.flatSuccessorSmallRestriction_encode c pres ((I0 ∪ I1) ∪ I2) T levels (natSetCode 2) tests F2
  have hLevels := M.stageThreeAssignmentLevels_mem pairing unions powers separation
    hI0 next.indices.index_ground next2.indices.index_ground data.terms_ground
  have conditions := M.stageThreeFlatPresentation_carrier_mem c I0 I1 action pres nodes d T T2 next2.valid1
    pairing unions powers separation collection hCarrier hOrder hNodes data.terms_ground
    next2.indices base directed next2.first rows hI0 next.indices.index_ground nodeOrder
    (M.omega_mem separation infinite)
  let values := fourFlatStageValues c.pairEmpty.carrier s.carrier pres.carrier pres3.carrier
  have ground := M.fourFlatStageHistory_mem c s pres pres3 pairing unions powers separation infinite
    rows data.lower_carrier_ground hCarrier conditions
  have selfCuts := fourFlatStageValues_self M c s pres pres3 I0 I1 I2 T
    first second next2.indices.levelCode F F2 F3
  have adjacent := fourFlatStageValues_adjacent M c s pres pres3 I0 I1 I2 T
    first second next2.indices.levelCode F F2 F3 r21 r32 code21 code32
  refine ⟨prior, F, hNodes, inputs, next2, hCarrier, hOrder, ground,
    finiteStageHistory_function values 4, ?_, threeRefinementHistory_function I0 I1 I2,
    threeRefinementHistory_indices I0 I1 I2, threeRefinementHistory_assignmentLevels I0 I1 I2 T, ?_, ?_⟩
  · exact M.threeRefinementHistory_mem pairing unions hI0 next.indices.index_ground next2.indices.index_ground
  · exact M.finiteFlatHistoryCoherence values 4 levels pairing unions powers separation
      (M.natSetCode_mem separation infinite 4) ground hLevels
      (fourFlatStageValues_flat M c s pres pres3 I0 I1 I2 T F F2 F3) selfCuts adjacent
  · exact M.fourFlatStageLimit_eq c s pres pres3 I0 I1 I2 T first second next2.indices.levelCode
      F F2 F3 r21 r32 code21 code32

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

theorem exists_rowStageThreeHistory
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
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
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
                (liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S valid)
                (fun p => rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p))
                nextAction ∧
              (letI := M.stageOneConditionSmallTop act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
               let nextPres := M.stageOneConditionPresentation act c s a lifted squared valid1
                 pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                 indexSystem ⊥ directed first collection
               StageThreeHistoryData M act c nextAction nextPres b s a ⊥ directed
                 lifted squared valid1 pairing unions powers separation collection
                 S mu s.nonbottom.carrier
                 (liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S valid)
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
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
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
  have original := fulfilled.exists_rowStageThreeNameLifting collection infinite choice hK standard indices
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
  let stageOneOrder := M.stageOneConditionSmallOrder act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder liftedGround ⊥ directed first collection
  obtain ⟨nextAction, equal, laws, wholeAction, wholeMaps, closed, support, priorAction⟩ := actionData
  refine ⟨nextAction, equal, laws, wholeAction, wholeMaps, closed, support, ?_⟩
  let stageOneTop := M.stageOneConditionSmallTop act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder liftedGround ⊥ directed first collection
  let nextPres := M.stageOneConditionPresentation act c s a lifted squared valid1
    pairing unions powers separation carrier forcingOrder geometry.carrier_ground liftedGround
    indexSystem ⊥ directed first collection
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S valid
  exact M.stageThreeHistoryData act c nextAction nextPres b s a ⊥ directed
    lifted squared valid1 pairing unions powers separation collection S mu s.nonbottom.carrier tuples
    (fun p => rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p))
    priorAction carrier indexSystem.index_ground order infinite

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
