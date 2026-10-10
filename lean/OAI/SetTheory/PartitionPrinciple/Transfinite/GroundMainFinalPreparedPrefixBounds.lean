import OAI.SetTheory.PartitionPrinciple.Forcing.GroundBinaryRowNameSupportBounds
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalStructuralSupportPreparation

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem prepared_prefix_term_bound
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
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
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
        (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      let prefixIndices := refinementDataHistoryIndices alpha lowerPacked
      let prefixAnchors := refinementIndexFieldGraph prefixIndices s.carrier 2
      let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
      ∀ (E : SetMembers geometry.carrier) (u : (M.nameDomain lower).names), u.val.val ∈ lifted →
      ∀ q0 : SetMembers Q,
      ∃ r : SetMembers Q, r ≤ q0 ∧
      ∃ (rowR : SetMembers c.carrier) (lowerA : ZFSet.{u}),
        lower.encode r = ZFSet.pair (c.encode rowR) lowerA ∧
        StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier (lower.encode r) ∧
      ∃ D0 : SetMembers geometry.carrier, E ≤ D0 ∧
        a.principalFix D0 ≤ localAct.stabilizer lower u.val ∧
        (∀ i : SetMembers geometry.carrier, s.encode i ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw rowR) → i ≤ D0) ∧
        (∀ z ∈ lowerA, ZFSet.pair z (s.encode D0) ∈
          stageOneDataBounds lowerA prefixIndices lifted S s.carrier mu s.nonbottom.carrier
            s.conditionOrder prefixAnchors tuples) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  intro alpha member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
  let subset := (And.left stagesOrdinal) alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  let lower := SetMembers.presentation Q
  let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset
  intro E u hu q0
  have packedEq := (M.structuralRefinementHistory_history_restrict b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared alpha history).trans
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared subset)
  have preparedResult : GroundSupportPreparedStrengtheningResult M c lifted alpha lowerPacked
      s.carrier (lower.encode q0) := by
    have actual := fulfilled.structural_support_prepared_strengthening
      collection infinite choice small smallD irreflexive columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      alpha (graphRestriction alpha history) hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
      cutOrdinal (trace.restrict cutOrdinal subset)
    dsimp only at actual
    rw [packedEq] at actual
    exact actual (lower.encode q0) (lower.encode_mem q0)
  obtain ⟨rawR, rawMember, belowQ0, supportsR, _hSupportsR, _supportsSubset, _smallSupports, prepared⟩ :=
    preparedResult
  let r : SetMembers Q := SetMembers.ofMem rawR rawMember
  have encodedR : lower.encode r = rawR := SetMembers.raw_ofMem rawR rawMember
  have rBelowQ0 : r ≤ q0 := by
    apply (lower.pair_mem_conditionOrder r q0).1
    rw [M.refinementHistoryDecodedOrder_eq]
    rw [encodedR]
    exact belowQ0
  obtain ⟨rawRow, rowMember, lowerA, _, rawCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier lifted alpha lowerPacked rawMember)
  let rowR := SetMembers.ofMem rawRow rowMember
  have rCode : lower.encode r = ZFSet.pair (c.encode rowR) lowerA :=
    encodedR.trans (rawCode.trans (congrArg (fun z => ZFSet.pair z lowerA)
      (SetMembers.raw_ofMem rawRow rowMember).symm))
  have preparedAt : StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier
      (lower.encode r) := encodedR.symm ▸ prepared.forget
  have countableBound : ∀ Z ∈ M.sets, Z ⊆ s.carrier → M.groundEmbeddable Z ZFSet.omega →
      ∃ X : SetMembers geometry.carrier, ∀ z : SetMembers geometry.carrier, s.encode z ∈ Z → z ≤ X :=
    geometry.decoded_countable_bound
      (fun Z hZ subset countable => (fulfilled.countable_localization Z hZ subset countable).2)
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation infinite choice
    coordinates two
  obtain ⟨_lowerGround, _lowerOrder, _maps, _lowerClosed, _terms, children⟩ :=
    M.semanticStructuralPrefix_preparation_inputs c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace member infinite choice rowClosed
  have restrictedMember : ZFSet.pair (c.encode rowR) lowerA ∈
      M.structuralForcingCarrier c.carrier b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared alpha (graphRestriction alpha history) := by
    change ZFSet.pair (c.encode rowR) lowerA ∈ M.refinementHistoryForcing c.carrier lifted alpha _
    rw [packedEq]
    exact rCode ▸ lower.encode_mem r
  obtain ⟨D0, rowBound, dataBound, eBelow, nameSupport⟩ :=
    M.binaryRowStructuralCondition_nameSupportBound s columns pairing unions powers separation collection
      infinite choice hL order hColumns directed countableBound hmu ⊤ valid hLifted b.carrier
      (supportBasisCode s b a.principalFix) squared alpha (graphRestriction alpha history)
      hG supports hSquared hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
      rowR lowerA restrictedMember lower localAct a ⊥ ![u.val, u.val]
      (fun i => Fin.cases (children u.val hu)
        (Fin.cases (children u.val hu) (fun j => Fin.elim0 j)) i) E
  rw [packedEq] at dataBound
  exact ⟨r, rBelowQ0, rowR, lowerA, rCode, preparedAt, D0, eBelow, nameSupport 0, rowBound, dataBound⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
