import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableRowSequenceReflection
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRawRefinementStageZF

namespace OAI



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

theorem exists_rowSemanticStructuralHistory
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
        lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          (∀ z ∈ lifted, IsName c.pairEmpty z) ∧ (∀ z ∈ squared, IsName c.pairEmpty z) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          ∀ stages ∈ M.sets, ordinalSetProperty stages → ∃ history ∈ M.sets,
            OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) stages history ∧
            M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
              (supportBasisCode s b a.principalFix) lifted squared stages history ∈ M.sets ∧
            RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted stages
              (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared stages history) ∧
            ∀ level P order top action,
              ZFSet.pair level (forcingStageCode P order top action) ∈ history →
              RawRefinementStageWitness M b s a ⊥ directed lifted squared level P order top action := by
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
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground order action
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, _, _, _, _, _, _, _, stageTerms⟩ :=
    fulfilled.exists_rowTermSystem collection infinite choice hK standard indices
  obtain ⟨ground, below, valid, children, _⟩ := stageTerms 0
  have closed := M.binaryRowTupleTerms_action a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action hmu cardinal.1
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid, ?_⟩
  exact M.pairEmpty_semanticStructuralHistory c act b s a ⊥ directed
    pairing unions powers separation collection carrier forcingOrder forcingAction
    geometry.actors_ground geometry.carrier_ground order action supports
    (M.omega_mem separation infinite) _ ground valid closed children






theorem exists_rowSemanticStructuralFinalHistory
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
        lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          (∀ z ∈ lifted, IsName c.pairEmpty z) ∧ (∀ z ∈ squared, IsName c.pairEmpty z) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          ∀ stages ∈ M.sets, ordinalSetProperty stages → ∃ history ∈ M.sets,
            OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) stages history ∧
            M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
              (supportBasisCode s b a.principalFix) lifted squared stages history ∈ M.sets ∧
            RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted stages
              (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared stages history) ∧
            (∀ level P order top action,
              ZFSet.pair level (forcingStageCode P order top action) ∈ history →
              RawRefinementStageWitness M b s a ⊥ directed lifted squared level P order top action) ∧
            ∃ P order top action,
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared stages history =
                  forcingStageCode P order top action ∧
              (P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets) ∧
              RawRefinementStageWitness M b s a ⊥ directed lifted squared stages P order top action := by
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
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground order action
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground action
  have original := fulfilled.exists_rowSemanticStructuralHistory collection infinite choice hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, valid, data⟩ := data
  obtain ⟨hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, histories⟩ := data
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, ?_⟩
  intro stages hStages ordinal
  obtain ⟨history, hHistory, trace, hPacked, historyRun, witnesses⟩ := histories stages hStages ordinal
  refine ⟨history, hHistory, trace, hPacked, historyRun, witnesses, ?_⟩
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  exact M.semanticStructuralCurrent_stage c act b s a ⊥ directed _ _ (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction
    geometry.actors_ground geometry.carrier_ground order action nodeMaps supports hLifted hSquared
    (M.omega_mem separation infinite) valid1 valid2 closed1 closed2 children1 children2
    (c.encode_mem ⊤) topRows hStages hHistory ordinal trace






theorem exists_rowSemanticStructuralSequenceReflection
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
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
        ∃ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
          (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
          (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
          (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
          (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
          (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
          (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau),
          graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          ∃ (history : ZFSet.{u}) (hHistory : history ∈ M.sets)
            (trace : OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) K history),
            M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
              (supportBasisCode s b a.principalFix) lifted squared K history ∈ M.sets ∧
            RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted K
              (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared K history) ∧
            (∀ level P order top action,
              ZFSet.pair level (forcingStageCode P order top action) ∈ history →
              RawRefinementStageWitness M b s a ⊥ directed lifted squared level P order top action) ∧
            ∃ P order top action,
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared K history =
                  forcingStageCode P order top action ∧
              (P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets) ∧
              RawRefinementStageWitness M b s a ⊥ directed lifted squared K P order top action ∧
              let coordinateGround := M.prod_mem pairing unions powers separation
                (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
              let nodeActionGround : a.actionGraph s b ∈ M.sets :=
                geometry.decoded_action_eq.symm ▸ geometry.action_ground
              let nodeOrderGround : s.conditionOrder ∈ M.sets :=
                geometry.decoded_order_eq.symm ▸ geometry.order_ground
              let forcingActionGround := M.internalRowActionGraph_mem a s b columns
                pairing unions powers separation infinite geometry.carrier_ground hColumns
                geometry.actors_ground nodeActionGround
              let supportGround := M.principalSupportBasis_mem a s b pairing unions powers separation
                geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
              let nodeMapsGround := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
                collection geometry.carrier_ground geometry.actors_ground nodeActionGround
              let topMem := c.encode_mem ⊤
              let topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
                intro row member
                obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
                exact (c.pair_mem_conditionOrder p ⊤).2 le_top
              let two := M.natSetCode_mem separation infinite 2
              let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinateGround two
              let forcingOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinateGround two
              let omega := M.omega_mem separation infinite
              let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared K history
              let Q := M.refinementHistoryForcing c.carrier lifted K packed
              let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ K}
              let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier lifted (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
              let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b) (supportBasisCode s b a.principalFix) lifted squared standard.1.1 trace
              let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
              let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared K history
                pairing unions powers separation collection geometry.actors_ground geometry.carrier_ground supportGround hHistory hLifted witnesses
              let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
                ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, lifted, squared, K, history]
                (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrderGround (Fin.cases supportGround
                  (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hK (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
              letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted K packed
              let upperAction := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
              letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
                M.refinementHistoryPartialOrder c.conditionOrder_code lifted j.val (graphRestriction j.val packed)
              let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
                (run).restriction standard.1.1 j.property.2.1 j.property.2.2 c.conditionOrder_code
              let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
                (run).inclusion standard.1.1 j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
                  hK hPacked hLifted j.property.1 carrier (c.encode ⊤) topMem topRows mono c.conditionOrder_code
              let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
                M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace j.val j.property.1
                  j.property.2.1 j.property.2.2 infinite choice
              let upperPres := SetMembers.presentation Q
              let F := a.principalSupportFamily ⊥ directed
              P = Q ∧
              ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
                H.mem p ∧ H.GenericFor (M.codedFamily upperPres) ∧
                H.GenericFor (formulaFamily (M.nameDomain upperPres)) ∧
                H.GenericFor (formulaFamily ((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F)) ∧
                (∀ j : Cuts,
                  ((projections j).projectedFilter H).GenericFor
                    (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier lifted j.val (graphRestriction j.val packed)))) ∧
                  ((projections j).projectedFilter H).GenericFor
                    (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier lifted j.val (graphRestriction j.val packed)))))) ∧
                M.sets ⊆ ((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F).values {q | H.mem q} ∧
                ZFRealization (((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F).values {q | H.mem q}) ∧
                (∀ U ∈ M.sets,
                  GroundSequenceReflection M (M.ordinaryExtension upperPres H) U ∧
                  GroundSequenceReflection M (M.symmetricExtension upperPres (upperAction) F H) U) := by
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
  have nodeActionGround : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have nodeOrderGround : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  have original := fulfilled.exists_rowSemanticStructuralFinalHistory collection infinite choice hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, valid, data⟩ := data
  obtain ⟨hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, histories⟩ := data
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2, hGraph, injection, ?_⟩
  obtain ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, action, code, fields, witness⟩ := histories K hK standard.1.1
  refine ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, action, code, fields, witness, ?_⟩
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  have canonical := M.structuralForcingStage_eq c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
    b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared K history
  have equalFields := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 (code.symm.trans canonical)
  refine ⟨equalFields.1, ?_⟩
  exact M.countableRow_semanticStructuralTrace_jointZF_sequenceReflection b s a ⊥ directed
    pairing unions powers separation collection infinite choice
    (ZFSet.prod s.nonbottom.carrier columns) coordinates small act lifted squared (c.encode ⊤)
    forcingAction geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround
    nodeMaps supports hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    (c.encode_mem ⊤) topRows K history hK hHistory standard.1.1 trace






theorem exists_rowSemanticStructuralZF
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
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
        lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          (∀ z ∈ lifted, IsName c.pairEmpty z) ∧ (∀ z ∈ squared, IsName c.pairEmpty z) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          ∃ history ∈ M.sets,
            OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) K history ∧
            M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
              (supportBasisCode s b a.principalFix) lifted squared K history ∈ M.sets ∧
            RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted K
              (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared K history) ∧
            (∀ level P order top action,
              ZFSet.pair level (forcingStageCode P order top action) ∈ history →
              RawRefinementStageWitness M b s a ⊥ directed lifted squared level P order top action) ∧
            ∃ P order top action,
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared K history =
                  forcingStageCode P order top action ∧
              (P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets) ∧
              RawRefinementStageWitness M b s a ⊥ directed lifted squared K P order top action ∧
              RawRefinementStageZF M b s a ⊥ directed lifted squared K P order top action := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground order action
  have original := fulfilled.exists_rowSemanticStructuralFinalHistory collection infinite choice hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, valid, data⟩ := data
  obtain ⟨hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, histories⟩ := data
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, ?_⟩
  obtain ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, forcingAction, code, fields, witness⟩ := histories K hK standard.1.1
  exact ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, forcingAction, code, fields, witness,
    witness.symmetricZF pairing unions powers separation collection infinite small
      fields.1 fields.2.1 geometry.actors_ground geometry.carrier_ground supports⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
