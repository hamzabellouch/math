import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAssignmentLabelDomainTotality

namespace OAI

open scoped ZFSet



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
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

include collection order nodeMaps supports

theorem binaryRowStructuralAssignmentImage_dataBound {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
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
    ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
      (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
      (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
      (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
      (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
      (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
      (_stagesOrdinal : ordinalSetProperty stages)
      (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let _carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let _forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let _forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let _omega := M.omega_mem separation infinite
    let _topMem := c.encode_mem ⊤
    let _topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared stages history
    let I := refinementDataHistoryIndices stages packed
    let anchors := refinementIndexFieldGraph I s.carrier 2
    ∀ (g : G) (D : L) (A : ZFSet.{u}), A ∈ M.sets →
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈ stageOneDataBounds A I lifted S s.carrier mu
        s.nonbottom.carrier s.conditionOrder anchors tuples) →
    let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode g) A
    movedA ∈ M.sets ∧
      stageOneDataBounds movedA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples ∈ M.sets ∧
      ∀ z ∈ movedA, ZFSet.pair z (s.encode (a.iso g D)) ∈
        stageOneDataBounds movedA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace coordinates two carrier forcingOrder
    forcingAction omega topMem topRows packed I anchors
  have hNonbottom := M.nonbottom_carrier_mem s separation hL
  have hS := M.rowPositionSequences_mem pairing unions powers separation hL order hNonbottom hmu
  have hTuples := M.binaryLiftedRowTupleFamily_mem pairing unions powers separation collection
    infinite hL order hNonbottom hC hmu ⊤ valid
  exact M.semanticStructuralAssignmentImage_dataBound c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace S mu tuples hS hmu hTuples
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun g f hf tau entry => ⟨M.rowPositionSequenceAction_mem a s b pairing unions powers separation
      hL hG graph hmu muOrdinal g hf,
      M.binaryLiftedRowTupleFamily_action a s b C pairing unions powers separation infinite
        hL hC hG graph hmu muOrdinal valid g f tau entry⟩)

end PartitionPilot.Forcing.TransitiveGround

end OAI
