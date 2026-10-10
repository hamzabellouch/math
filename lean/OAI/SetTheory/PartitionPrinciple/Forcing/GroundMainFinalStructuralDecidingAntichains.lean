import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralFinalRefinements
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalStructuralSizeFamilies

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
open scoped ZFSet
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

theorem exists_rowSemanticStructuralAntichainHistory
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
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
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
              (∀ beta ∈ K,
                GroundBelow M (refinementDataHistoryIndices beta (graphRestriction beta packed)) K ∧
                GroundBelow M (M.refinementHistoryForcing c.carrier lifted beta
                  (graphRestriction beta packed)) K) ∧
              M.groundEmbeddable (refinementDataHistoryIndices K packed) K ∧
              (∀ D ∈ M.sets, GroundBelow M D K → D ⊆ Q →
                ∃ beta ∈ K, ∀ row A, ZFSet.pair row A ∈ D →
                  assignmentCut (refinementDataHistoryLevels K packed lifted) beta A = A ∧
                  ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted beta
                    (graphRestriction beta packed)) ∧
              (∀ E ∈ M.sets, OrderAntichainCode Q
                (M.refinementHistoryOrder c.carrier c.conditionOrder lifted K packed) E →
                  GroundBelow M E K) ∧
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
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  have original := fulfilled.exists_rowSemanticStructuralSizeFamilyHistory
    collection infinite choice small hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, valid, data⟩ := data
  obtain ⟨hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2,
    hGraph, injection, history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, action, code, fields, witness, final⟩ := data
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  have conditions := standard.to_conditions pairing unions powers separation hK
  have nodeSize : GroundBelow M s.carrier K := (run.finalGeometry_below i₀ choice hK standard indices).1
  have hPositions := M.nonbottom_carrier_mem s separation geometry.carrier_ground
  have positionSize : GroundBelow M s.nonbottom.carrier K :=
    nodeSize.restrict separation hPositions hK (fun z member => (s.mem_nonbottom_carrier z).1 member |>.1)
  have columnSize := conditions.groundOmegaOne_below pairing unions powers separation collection infinite hK
  have rowSize : GroundBelow M c.carrier K :=
    GroundBelow.binaryRowCarrier pairing unions powers separation hPositions hColumns hK
      conditions positionSize columnSize
  have coordinates := M.prod_mem pairing unions powers separation hPositions hColumns
  have carrier : c.carrier ∈ M.sets := M.countablePartialFunctions_mem
    pairing unions powers separation infinite coordinates (M.natSetCode_mem separation infinite 2)
  have liftedSize : GroundBelow M lifted K := M.pairEmpty_renamedFamily_below c
    pairing unions powers separation collection carrier ground hK valid below
  let directed := geometry.decoded_directed fulfilled.directed
  have forcingOrderGround : c.conditionOrder ∈ M.sets :=
    M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates
      (M.natSetCode_mem separation infinite 2)
  have forcingActionGround : act.actionGraph c b ∈ M.sets :=
    M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  have nodeMapsGround := M.conditionMapFamily_mem_of_actionGraph a s b
    pairing unions powers separation collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  have topMem := c.encode_mem ⊤
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  have antichains := M.semanticStructuralTrace_antichains_below c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection
    carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground
    nodeOrderGround nodeActionGround nodeMapsGround supports hLifted hSquared
    (M.omega_mem separation infinite) valid1 valid2 closed1 closed2 children1 children2 topMem topRows
    hK hHistory conditions trace infinite choice rowSize liftedSize
  dsimp only
  exact ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2, hGraph, injection,
    history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, action, code, fields, witness, final.1, final.2.1,
    final.2.2.1, final.2.2.2.1, antichains, final.2.2.2.2⟩






theorem exists_rowSemanticStructuralDecidingAntichainHistory
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
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
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
              (∀ beta ∈ K,
                GroundBelow M (refinementDataHistoryIndices beta (graphRestriction beta packed)) K ∧
                GroundBelow M (M.refinementHistoryForcing c.carrier lifted beta
                  (graphRestriction beta packed)) K) ∧
              M.groundEmbeddable (refinementDataHistoryIndices K packed) K ∧
              (∀ D ∈ M.sets, GroundBelow M D K → D ⊆ Q →
                ∃ beta ∈ K, ∀ row A, ZFSet.pair row A ∈ D →
                  assignmentCut (refinementDataHistoryLevels K packed lifted) beta A = A ∧
                  ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted beta
                    (graphRestriction beta packed)) ∧
              (∀ E ∈ M.sets, OrderAntichainCode Q
                (M.refinementHistoryOrder c.carrier c.conditionOrder lifted K packed) E →
                  GroundBelow M E K) ∧
              (let finalOrder := M.refinementHistoryOrder c.carrier c.conditionOrder lifted K packed
                ∀ J ∈ M.sets, GroundBelow M J K → (∀ sigma ∈ J, IsName upperPres sigma) →
                  ∀ tau : (M.nameDomain upperPres).names,
                    ∃ f ∈ M.sets, ZFSet.IsFunc J (M.groundPower Q) f ∧
                      (∀ sigma A, ZFSet.pair sigma A ∈ f →
                        RelativeMaximalAntichainCode Q finalOrder
                          (M.ordinaryMembershipDecisions Q finalOrder sigma tau.val.val) A ∧
                        ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
                          ZFSet.pair r q ∈ finalOrder ∧ ZFSet.pair r p ∈ finalOrder) ∧
                      let U := ⋃₀ relationImage J (M.groundPower Q) f
                      (U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ Q) ∧
                      ∃ beta ∈ K,
                        (∀ row B, ZFSet.pair row B ∈ U →
                          assignmentCut (refinementDataHistoryLevels K packed lifted) beta B = B ∧
                          ZFSet.pair row B ∈ M.refinementHistoryForcing c.carrier lifted beta (graphRestriction beta packed)) ∧
                        ∀ sigma A, ZFSet.pair sigma A ∈ f →
                          let lower := M.refinementHistoryForcing c.carrier lifted beta (graphRestriction beta packed)
                          let lowerOrder := M.refinementHistoryOrder c.carrier c.conditionOrder lifted beta
                            (graphRestriction beta packed)
                          A ⊆ lower ∧ ∀ q ∈ lower, ∃ p ∈ A, ∃ r ∈ lower,
                            ZFSet.pair r q ∈ lowerOrder ∧ ZFSet.pair r p ∈ lowerOrder) ∧
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
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  have original := fulfilled.exists_rowSemanticStructuralAntichainHistory
    collection infinite choice small hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, valid, data⟩ := data
  obtain ⟨hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2,
    hGraph, injection, history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, action, code, fields, witness, final⟩ := data
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  have conditions := standard.to_conditions pairing unions powers separation hK
  have nodeSize : GroundBelow M s.carrier K := (run.finalGeometry_below i₀ choice hK standard indices).1
  have hPositions := M.nonbottom_carrier_mem s separation geometry.carrier_ground
  have positionSize : GroundBelow M s.nonbottom.carrier K :=
    nodeSize.restrict separation hPositions hK (fun z member => (s.mem_nonbottom_carrier z).1 member |>.1)
  have columnSize := conditions.groundOmegaOne_below pairing unions powers separation collection infinite hK
  have rowSize : GroundBelow M c.carrier K :=
    GroundBelow.binaryRowCarrier pairing unions powers separation hPositions hColumns hK
      conditions positionSize columnSize
  have coordinates := M.prod_mem pairing unions powers separation hPositions hColumns
  have carrier : c.carrier ∈ M.sets := M.countablePartialFunctions_mem
    pairing unions powers separation infinite coordinates (M.natSetCode_mem separation infinite 2)
  have liftedSize : GroundBelow M lifted K := M.pairEmpty_renamedFamily_below c
    pairing unions powers separation collection carrier ground hK valid below
  let directed := geometry.decoded_directed fulfilled.directed
  have forcingOrderGround : c.conditionOrder ∈ M.sets :=
    M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates
      (M.natSetCode_mem separation infinite 2)
  have forcingActionGround : act.actionGraph c b ∈ M.sets :=
    M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  have nodeMapsGround := M.conditionMapFamily_mem_of_actionGraph a s b
    pairing unions powers separation collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  have topMem := c.encode_mem ⊤
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  have deciding := M.semanticStructuralTrace_membershipAntichains_prefix c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection
    carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground
    nodeOrderGround nodeActionGround nodeMapsGround supports hLifted hSquared
    (M.omega_mem separation infinite) valid1 valid2 closed1 closed2 children1 children2 topMem topRows
    hK hHistory conditions trace infinite choice rowSize liftedSize
  dsimp only
  exact ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2, hGraph, injection,
    history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, action, code, fields, witness, final.1, final.2.1,
    final.2.2.1, final.2.2.2.1, final.2.2.2.2.1, deciding, final.2.2.2.2.2⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
