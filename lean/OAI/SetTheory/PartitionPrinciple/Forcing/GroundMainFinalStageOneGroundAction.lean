import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneNameLiftFamilies
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalStageOneClosure

namespace OAI

open scoped ZFSet

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

theorem exists_rowStageOneActionInputs
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
        (∃ hLifted : lifted ∈ M.sets, squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          ∃ valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z,
          ∃ valid2 : ∀ z ∈ squared, IsName c.pairEmpty z,
            ∃ first : NiceNameSystem M act c.pairEmpty s a ⊥ directed lifted valid1,
            NiceNameSystem M act c.pairEmpty s a ⊥ directed squared valid2 ∧
            ∃ indexSystem : NiceRefinementIndexSystem M act c.pairEmpty s a ∅ lifted squared valid1 valid2,
            StageOneActionParameters M act c.pairEmpty b s a lifted squared valid1 ∧
            M.stageOneForcing act c s a lifted squared valid1 ∈ M.sets ∧
            M.stageOneForcingOrder act c s a lifted squared valid1 ∈ M.sets ∧
            (letI := M.stageOneConditionSmallOrder act c s a lifted squared valid1
              pairing unions powers separation hRow hOrder hLifted ⊥ directed first collection
             InternallyCountablyClosed M
              (M.stageOneConditionPresentation act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                indexSystem ⊥ directed first collection)) ∧
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
  have original := fulfilled.exists_rowStageOneClosure collection infinite choice hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, data⟩ := data
  refine data.elim (fun valid data => ?_)
  refine data.elim (fun liftedGround data => ?_)
  obtain ⟨squaredGround, graphGround, injection, data⟩ := data
  refine data.elim (fun valid1 data => ?_)
  refine data.elim (fun valid2 data => ?_)
  refine data.elim (fun first data => ?_)
  obtain ⟨second, data⟩ := data
  refine data.elim (fun indexSystem data => ?_)
  obtain ⟨forcingGround, orderGround, closed, objects, finitePowers⟩ := data
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  have conditionMaps := M.pairEmpty_conditionMapFamily_mem pairing unions powers separation c act b collection
    carrier geometry.actors_ground forcingAction
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation collection
    geometry.carrier_ground geometry.actors_ground action
  have termClosed := M.binaryRowTupleTerms_action a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action hmu cardinal.1
  have liftedClosed := Name.renamedFamily_closed act c.pairEmpty _ valid termClosed
  have squaredClosed := orderedPairNameFamily_closed act valid1 valid1 liftedClosed liftedClosed
  have familyGround := M.familySet_mem c.pairEmpty ⊤ pairing unions powers separation liftedGround
    (M.transitive (M.pairEmpty_carrier_mem pairing unions powers separation c carrier)
      (c.pairEmpty.encode_mem ⊤)) valid1
  exact ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    liftedGround, squaredGround, graphGround, injection, valid1, valid2,
    first, second, indexSystem, ⟨conditionMaps, nodeMaps, liftedClosed, squaredClosed, familyGround⟩,
    forcingGround, orderGround, closed, objects, finitePowers⟩

theorem exists_rowStageOneAction
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
              InternallyCountablyClosed M
              (M.stageOneConditionPresentation act c s a lifted squared valid1
                pairing unions powers separation hRow hOrder geometry.carrier_ground hLifted
                indexSystem ⊥ directed first collection)) ∧
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
  have original := fulfilled.exists_rowStageOneActionInputs collection infinite choice hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, data⟩ := data
  refine data.elim (fun valid data => ?_)
  refine data.elim (fun liftedGround data => ?_)
  obtain ⟨squaredGround, graphGround, injection, data⟩ := data
  refine data.elim (fun valid1 data => ?_)
  refine data.elim (fun valid2 data => ?_)
  refine data.elim (fun first data => ?_)
  obtain ⟨second, data⟩ := data
  refine data.elim (fun indexSystem data => ?_)
  obtain ⟨inputs, forcingGround, orderGround, closed, objects, finitePowers⟩ := data
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  have originalMaps := M.conditionMapFamily_mem_of_actionGraph act c b pairing unions powers separation
    collection carrier geometry.actors_ground forcingAction
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    liftedGround, squaredGround, graphGround, injection, valid1, valid2,
    first, second, indexSystem, inputs, originalMaps,
    forcingGround, orderGround, ?_, objects, finitePowers⟩
  let lifted := Name.renamedFamily c.pairEmpty id _ valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let := M.stageOneConditionSmallOrder act c s a lifted squared valid1 pairing unions powers separation
    carrier forcingOrder liftedGround ⊥ directed first collection
  exact ⟨M.stageOneSmallAction act c s a lifted squared valid1 pairing unions powers separation
      carrier forcingOrder liftedGround indexSystem ⊥ directed first collection b inputs
      squaredGround (M.omega_mem separation infinite), rfl,
    M.stageOneSmallAction_laws act c s a lifted squared valid1 pairing unions powers separation
      carrier forcingOrder geometry.carrier_ground liftedGround indexSystem ⊥ directed first
      collection b inputs squaredGround (M.omega_mem separation infinite), closed⟩

theorem exists_rowStageOneGroundAction
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
                indexSystem ⊥ directed first collection)) ∧
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
  have original := fulfilled.exists_rowStageOneAction collection infinite choice hK standard indices
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
  obtain ⟨nextAction, equal, laws, closed⟩ := actionData
  refine ⟨nextAction, equal, laws, ?_, ?_, closed⟩
  · rw [equal]
    exact M.stageOneSmallActionGraph_mem act c s a lifted squared valid1 pairing unions powers separation
      carrier forcingOrder geometry.carrier_ground liftedGround indexSystem ⊥ directed first collection
      b inputs squaredGround (M.omega_mem separation infinite) order geometry.actors_ground originalMaps
  · rw [equal]
    exact M.stageOneSmallActionMapFamily_mem act c s a lifted squared valid1 pairing unions powers separation
      carrier forcingOrder geometry.carrier_ground liftedGround indexSystem ⊥ directed first collection
      b inputs squaredGround (M.omega_mem separation infinite) order geometry.actors_ground originalMaps

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
