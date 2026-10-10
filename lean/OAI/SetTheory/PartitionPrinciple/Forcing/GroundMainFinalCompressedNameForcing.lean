import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalStructuralCompression

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

theorem structural_compressed_name_forcing
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
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
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ {n : Nat} (phi : SetFormula (n + 1)) (tau : (M.nameDomain upper).names)
    (tail : Fin n → (M.nameDomain upper).names) (V E : SetMembers geometry.carrier)
    (p : SetMembers upperQ), V < E →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) tau.val →
    (∀ j, a.principalFix V ≤ upperAct.stabilizer upper (tail j).val) →
    Forces (M.nameDomain upper) phi (extend tau tail) p →
    ∃ g : SetMembers geometry.actors, g ∈ a.principalFix V ∧
    ∃ sigma : (M.nameDomain upper).names,
      sigma.val = upperAct.act upper g tau.val ∧
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) sigma.val ∧
      a.principalFix E ≤ upperAct.stabilizer upper sigma.val ∧
    ∃ r q : SetMembers upperQ,
      r ≤ p ∧ StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw r) ∧
      q ≤ r ∧ q ≤ upperAct.iso g r ∧ q ≤ p ∧ q ≤ upperAct.iso g p ∧
      Forces (M.nameDomain upper) phi (extend sigma tail) q := by
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro upperAct upper n phi tau tail V E p strict hsTau fixedTail forced
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
  have closed : ∀ g nu, nu ∈ (M.nameDomain upper).names →
      upperAct.act upper g nu ∈ (M.nameDomain upper).names :=
    M.act_mem upper upperAct b pairing unions powers separation collection hQ maps
  obtain ⟨B, supportTau⟩ := hsTau.symmetric
  obtain ⟨rawR, memberR, belowRaw, support, _hSupport, _subsetSupport, _smallSupport, prepared⟩ :=
    fulfilled.structural_support_prepared_strengthening collection infinite choice small smallD
      irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace (SetMembers.raw p) (SetMembers.raw_mem p)
  let r : SetMembers upperQ := SetMembers.ofMem rawR memberR
  have rRaw : SetMembers.raw r = rawR := SetMembers.raw_ofMem _ _
  have below : r ≤ p := by
    change ZFSet.pair (SetMembers.raw r) (SetMembers.raw p) ∈ _
    rw [rRaw]
    exact belowRaw
  have preparedR : StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier
      (SetMembers.raw r) := by
    rw [rRaw]
    exact prepared.forget
  let sourceRow := M.refinementHistoryRowFunction c lifted stages packed r
  obtain ⟨A, rCode⟩ := M.refinementHistoryRowFunction_coordinates c lifted stages packed r
  obtain ⟨dBound, vd, bd, usedD, dataD⟩ := fulfilled.toFinalFulfillment.structural_bounds_with
    collection infinite choice columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    r sourceRow A V B rCode
  have condition : ZFSet.pair (c.encode sourceRow) A ∈ upperQ := rCode ▸ SetMembers.raw_mem r
  have preparedCode : StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier
      (ZFSet.pair (c.encode sourceRow) A) := rCode ▸ preparedR
  obtain ⟨g, cap, fixed, _strictCap, capE, movedD, commonRow, _rowCode, memberQ, toR, toMovedR⟩ :=
    fulfilled.structural_compression collection infinite choice labels small columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace sourceRow A condition preparedCode V E dBound
      strict vd usedD dataD
  let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode g) A
  let rawQ := ZFSet.pair (c.encode commonRow) (A ∪ movedA)
  let q : SetMembers upperQ := SetMembers.ofMem rawQ memberQ
  have qRaw : SetMembers.raw q = rawQ := SetMembers.raw_ofMem _ _
  have qr : q ≤ r := by
    change ZFSet.pair (SetMembers.raw q) (SetMembers.raw r) ∈ _
    rw [qRaw, rCode]
    exact toR
  have movedCode : SetMembers.raw (upperAct.iso g r) =
      ZFSet.pair (c.encode (act.iso g sourceRow)) movedA :=
    M.semanticStructuralAction_coordinates c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace g r sourceRow A rCode
  have qgr : q ≤ upperAct.iso g r := by
    change ZFSet.pair (SetMembers.raw q) (SetMembers.raw (upperAct.iso g r)) ∈ _
    rw [qRaw, movedCode]
    exact toMovedR
  let sigma : (M.nameDomain upper).names := ⟨upperAct.act upper g tau.val, closed g tau.val tau.property⟩
  have supported : a.principalFix E ≤ upperAct.stabilizer upper sigma.val :=
    upperAct.compressed_name_support upper a g dBound E tau.val
      ((a.principalFix_antitone bd).trans supportTau) (movedD.trans capE)
  have forcedR := forces_mono (M.nameDomain upper) phi (extend tau tail) forced below
  have translated := (upperAct.formula_forces_act_iff upper (M.nameDomain upper) closed g
    phi (extend tau tail) r).2 forcedR
  have envEq : upperAct.actAssignment upper (M.nameDomain upper) closed g (extend tau tail) =
      extend sigma tail := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · apply Subtype.ext
      exact fixedTail i fixed
  rw [envEq] at translated
  exact ⟨g, fixed, sigma, rfl, hsTau.translated g, supported,
    r, q, below, preparedR, qr, qgr, qr.trans below,
    qgr.trans ((upperAct.iso g).monotone below),
    forces_mono (M.nameDomain upper) phi (extend sigma tail) translated qgr⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
