import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBinaryRowRecordedPreparationBounds

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
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
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (countable_bound : ∀ W ∈ M.sets, W ⊆ s.carrier → M.groundEmbeddable W ZFSet.omega →
  ∃ D : L, ∀ x : L, s.encode x ∈ W → x ≤ D)
include order choice countable_bound

theorem binaryRowStructuralPositionSupport {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (muOrdinal : ordinalSetProperty mu) :
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
    ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
      (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (stagesOrdinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared stages history
    let J := refinementDataHistoryIndices stages packed
    let anchors := refinementIndexFieldGraph J s.carrier 2
    let Q := M.refinementHistoryForcing c.carrier lifted stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
    let actual := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace
    ∀ (q : SetMembers Q) (p : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u}),
      SetMembers.raw q = ZFSet.pair (c.encode p) A →
    ∀ extra ∈ M.sets, extra ⊆ s.carrier → M.groundEmbeddable extra ZFSet.omega →
    ∃ D : L, ∃ f ∈ M.sets, ∃ W ∈ M.sets,
      ZFSet.IsFunc A s.carrier f ∧
      f ⊆ stageOneDataBounds A J lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∧
      W = (relationImage A s.carrier f ∪
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p)) ∪ extra ∧
      W ⊆ s.carrier ∧ M.groundEmbeddable W ZFSet.omega ∧
      (∀ x : L, s.encode x ∈ W → x ≤ D) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A J lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
      (∀ x : L, s.encode x ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → x ≤ D) ∧
      (∀ x : L, s.encode x ∈ extra → x ≤ D) ∧
      (∀ g ∈ a.principalFix D, actual.iso g q = q) := by
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace coordinates two carrier forcingOrder
    forcingAction omega topMem topRows packed J anchors Q
  let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro actual q p A code extra hExtra extraSubset extraSmall
  have member := code ▸ SetMembers.raw_mem q
  have candidate := (M.mem_refinementHistoryForcing c.carrier lifted stages packed _).1 member |>.1
  have small := (ZFSet.pair_mem_prod.1 candidate).2
  obtain ⟨D, f, hf, W, hW, function, selected, equal, subset, smallW, bounded,
      dataBound, rowBound, extraBound⟩ :=
    M.binaryRowStructuralDataSelection s C pairing unions powers separation collection infinite choice
      hL order hC directed countable_bound hmu ⊤ valid hLifted b.carrier
      (supportBasisCode s b a.principalFix) squared stages history hG supports hSquared hs hh
      p A small extra hExtra extraSubset extraSmall
  refine ⟨D, f, hf, W, hW, function, selected, equal, subset, smallW, bounded,
    dataBound, rowBound, extraBound, ?_⟩
  intro g actor
  apply M.semanticStructuralCondition_fixed_of_dataBound c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace S mu s.nonbottom.carrier tuples D
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun f _ u entry bound => M.liftedRowTuple_supported a s b C pairing unions powers separation
      infinite hL hC hG graph hmu muOrdinal valid f u D entry bound.2)
    g actor q p A code
  · exact M.internalRowAction_eq_of_principalFix a s b C pairing unions powers separation infinite
      hL hC hG graph g p D (fun i used => rowBound i.val used) actor
  · exact dataBound

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

theorem exists_rowSemanticStructuralPositionSupportHistory
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
          ∀ (stages : ZFSet.{u}) (hStages : stages ∈ M.sets) (ordinal : ordinalSetProperty stages),
          ∃ (history : ZFSet.{u}) (hHistory : history ∈ M.sets)
            (trace : OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
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
              RawRefinementStageWitness M b s a ⊥ directed lifted squared stages P order top action ∧
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
                (supportBasisCode s b a.principalFix) lifted squared stages history
              let Q := M.refinementHistoryForcing c.carrier lifted stages packed
              let J := refinementDataHistoryIndices stages packed
              let anchors := refinementIndexFieldGraph J s.carrier 2
              let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
                (⋃₀ ⋃₀ rows) rows S valid
              letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
              let actual := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
                pairing unions powers separation collection carrier forcingOrderGround forcingActionGround
                geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround
                supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
                topMem topRows hStages hHistory ordinal trace
              P = Q ∧
              ∀ (p : SetMembers (M.smallPartialFunctions
                  (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)) (A : ZFSet.{u})
                (member : ZFSet.pair (c.encode p) A ∈ Q),
              let q : SetMembers Q := SetMembers.ofMem (ZFSet.pair (c.encode p) A) member
              ∀ extra ∈ M.sets, extra ⊆ s.carrier → M.groundEmbeddable extra ZFSet.omega →
              ∃ E : SetMembers geometry.carrier, ∃ f ∈ M.sets, ∃ W ∈ M.sets,
                ZFSet.IsFunc A s.carrier f ∧
                f ⊆ stageOneDataBounds A J lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∧
                W = (relationImage A s.carrier f ∪
                  rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p)) ∪ extra ∧
                W ⊆ s.carrier ∧ M.groundEmbeddable W ZFSet.omega ∧
                (∀ x : SetMembers geometry.carrier, s.encode x ∈ W → x ≤ E) ∧
                (∀ z ∈ A, ZFSet.pair z (s.encode E) ∈
                  stageOneDataBounds A J lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) ∧
                (∀ x : SetMembers geometry.carrier,
                  s.encode x ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p) → x ≤ E) ∧
                (∀ x : SetMembers geometry.carrier, s.encode x ∈ extra → x ≤ E) ∧
                (∀ g ∈ a.principalFix E, actual.iso g q = q) := by
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
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground order action
  have countableBound := geometry.decoded_countable_bound
    (fun W hW subset small => (fulfilled.countable_localization W hW subset small).2)
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground action
  have original := fulfilled.exists_rowSemanticStructuralFinalHistory collection infinite choice hK standard indices
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid, data⟩ := original
  obtain ⟨hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, histories⟩ := data
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2, hGraph, injection, ?_⟩
  intro stages hStages ordinal
  obtain ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, stageOrder, top, stageAction, code, fields, witness⟩ := histories stages hStages ordinal
  refine ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, stageOrder, top, stageAction, code, fields, witness, ?_⟩
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  have canonical := M.structuralForcingStage_eq c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
    b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stages history
  have equalFields := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 (code.symm.trans canonical)
  refine ⟨equalFields.1, ?_⟩
  intro p A member extra hExtra extraSubset extraSmall
  exact M.binaryRowStructuralPositionSupport a s b columns pairing unions powers separation collection infinite choice
    geometry.carrier_ground order hColumns geometry.actors_ground action nodeMaps supports directed countableBound
    hmu cardinal.1 valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hStages hHistory ordinal trace (SetMembers.ofMem (ZFSet.pair (c.encode p) A) member) p A (SetMembers.raw_ofMem _ _)
    extra hExtra extraSubset extraSmall

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end

end OAI
