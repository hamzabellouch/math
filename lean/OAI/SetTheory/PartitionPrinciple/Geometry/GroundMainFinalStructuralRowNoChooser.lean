import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticOrdinalRowOrbitCovers
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

theorem structural_lifted_rows_no_chooser
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable columns ZFSet.omega)
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
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
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  let recursive := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let inclusion := M.refinementHistoryRowEmbedding c lifted stages packed recursive stagesOrdinal carrier
  ∀ (H : ConditionFilter (SetMembers upperQ)),
    H.GenericFor (formulaFamily (M.nameDomain upper)) →
    let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
    let rowSet := Name.eval {p | H.mem p}
      (Name.rename upper inclusion (M.internalRowSetName s columns hL))
    rowSet ∈ N.sets ∧
      ¬ ∃ f ∈ N.sets, ∀ S ∈ N.sets, S ⊆ rowSet → S.Nonempty →
        ∃ x ∈ S, ZFSet.pair S x ∈ f ∧ ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x := by
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
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
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  let recursive := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let inclusion := M.refinementHistoryRowEmbedding c lifted stages packed recursive stagesOrdinal carrier
  intro H ordinary
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection hG hL order graph supports hLifted hSquared hs hh
  have hGraph : upperAct.actionGraph upper b ∈ M.sets := by
    erw [M.semanticStructuralAction_graph]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection hG hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments forcingAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b pairing unions powers separation
    collection hQ hG hGraph
  have projectionData := M.semanticStructuralTrace_rowProjection c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder
    forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega
    valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace
    infinite choice
  have rowSetGround := M.liftedInternalRowSet_mem a s b columns directed pairing unions powers
    separation collection infinite hL hC hG graph upper upperAct hQ inclusion
    projectionData.2.2.1 projectionData.2.2.2.2.2.2 H
  refine ⟨rowSetGround, ?_⟩
  rintro ⟨f, hf, selection⟩
  obtain ⟨B, i, sn, xn, fn, outside, snCode, xnCode, fixedS, fixedF, p0, _hp0, forced0⟩ :=
    M.liftedInternalRows_chooser_witness a s b columns directed pairing unions powers separation
      collection infinite hL hC hG graph upper upperAct hQ order
      (geometry.decoded_unbounded fulfilled.growth)
      (M.refinementHistoryRowRestriction c lifted stages packed) inclusion projectionData.1
      projectionData.2.2.1 projectionData.2.2.2.2.2.2 H ordinary f hf selection
  obtain ⟨rawP, memberP, belowRaw, support, _hSupport, _subsetSupport, _smallSupport, prepared⟩ :=
    fulfilled.structural_support_prepared_strengthening collection infinite choice small smallD
      irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace (SetMembers.raw p0) (SetMembers.raw_mem p0)
  let p : SetMembers upperQ := SetMembers.ofMem rawP memberP
  have pRaw : SetMembers.raw p = rawP := SetMembers.raw_ofMem _ _
  have below : p ≤ p0 := by
    change ZFSet.pair (SetMembers.raw p) (SetMembers.raw p0) ∈ _
    rw [pRaw]
    exact belowRaw
  have forced := forces_mono (M.nameDomain upper) (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula
    (extend sn (extend xn (extend fn Fin.elim0))) forced0 below
  have preparedP : StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier
      (SetMembers.raw p) := by
    rw [pRaw]
    exact prepared.forget
  let sourceRow := M.refinementHistoryRowFunction c lifted stages packed p
  obtain ⟨A, pCode⟩ := M.refinementHistoryRowFunction_coordinates c lifted stages packed p
  obtain ⟨dBound, bd, id, usedD, dataD⟩ := fulfilled.toFinalFulfillment.structural_bounds_with
    collection infinite choice columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    p sourceRow A B i.val pCode
  have descent := fulfilled.structural_prefix_descent collection infinite choice small smallD
    irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace
  obtain ⟨g, fixed, overlap, _overlap1, _overlap2, row, result, _rowCode, _resultCode, toP, toMoved⟩ :=
    fulfilled.toFinalFulfillment.structural_separating_copy_union collection infinite choice small
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace
      p p sourceRow sourceRow A A 1 1 dBound dBound B pCode pCode preparedP
      (by change p ≤ upperAct.iso 1 p; rw [upperAct.one]) usedD usedD dataD dataD bd
      (a.principalFix B).one_mem (a.principalFix B).one_mem
      (by change a.iso 1 dBound ≤ dBound; rw [a.one]) (by change a.iso 1 dBound ≤ dBound; rw [a.one]) descent
  have distinctNode : a.iso g i.val ≠ i.val := a.moved_ne_of_separated g B dBound i.val
    (fun x xd xg => by
      rw [← overlap]
      exact geometry.meet.toSmallMeetOrder.le_meet xg xd) id outside
  have movedCode : upperAct.act upper g xn.val =
      Name.rename upper inclusion (M.internalRowName s columns hL (a.nonbottom.iso g i)) := by
    rw [xnCode, act.act_rename_of_equivariant upperAct c upper inclusion
      projectionData.2.2.2.2.2.2,
      M.internalRowName_action a s b columns pairing unions powers separation infinite hL hC hG graph]
  exact M.projectedBinaryRows_uniqueFiber_incompatible upper b upperAct
    (a.principalSupportFamily ⊥ directed) pairing unions powers separation collection infinite choice
    small (M.nonbottom_carrier_mem s separation hL) hC uncountable hQ maps
    (M.refinementHistoryRowRestriction c lifted stages packed) inclusion projectionData.1
    projectionData.2.1 ⊤ (fun _ => le_top) sn xn fn g (fixedS fixed) (fixedF fixed)
    (s.encode i.val) (s.nonbottom.encode_mem i)
    (s.encode (a.iso g i.val)) (s.nonbottom.encode_mem (a.nonbottom.iso g i))
    (fun equal => distinctNode (s.injective equal).symm) xnCode movedCode p forced
    ⟨result, toP, toMoved⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
