import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAlignedRectangleUnions
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalRectangleActionData
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalStructuralPositionSupport
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalRowRectangles

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

theorem structural_bounds_with
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
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
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
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
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  ∀ (q : SetMembers upperQ) (row : SetMembers c.carrier) (A : ZFSet.{u})
    (U V : SetMembers geometry.carrier),
    SetMembers.raw q = ZFSet.pair (c.encode row) A →
    ∃ X : SetMembers geometry.carrier, U ≤ X ∧ V ≤ X ∧
      (∀ i : SetMembers geometry.carrier,
        s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) → i ≤ X) ∧
      (∀ z ∈ A, ZFSet.pair z (s.encode X) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) := by
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  intro q row A U V code
  have countableBound : ∀ Z ∈ M.sets, Z ⊆ s.carrier → M.groundEmbeddable Z ZFSet.omega →
      ∃ X : SetMembers geometry.carrier, ∀ z : SetMembers geometry.carrier, s.encode z ∈ Z → z ≤ X :=
    geometry.decoded_countable_bound
      (fun Z hZ subset countable => (fulfilled.countable_localization Z hZ subset countable).2)
  let extra : ZFSet.{u} := {s.encode U, s.encode V}
  have groundU := M.transitive hL (s.encode_mem U)
  have groundV := M.transitive hL (s.encode_mem V)
  have extraGround : extra ∈ M.sets := M.unorderedPair_mem pairing groundU groundV
  have extraSubset : extra ⊆ s.carrier := by
    intro z member
    rcases ZFSet.mem_pair.1 member with rfl | rfl
    · exact s.encode_mem U
    · exact s.encode_mem V
  have emptyGround := M.empty_mem ⟨s.carrier, hL⟩
  have firstSmall := M.groundEmbeddable_insert pairing unions powers separation infinite emptyGround groundV
    (M.empty_groundEmbeddable ZFSet.omega ⟨s.carrier, hL⟩)
  have firstGround := M.insert_mem pairing unions groundV emptyGround
  have extraSmall : M.groundEmbeddable extra ZFSet.omega := by
    exact M.groundEmbeddable_insert pairing unions powers separation infinite
      firstGround groundU firstSmall
  obtain ⟨X, _f, _hf, _W, _hW, _function, _selected, _equal, _subset, _small,
      _bounded, dataBound, rowBound, extraBound, _fixed⟩ :=
    M.binaryRowStructuralPositionSupport a s b columns pairing unions powers separation collection infinite
      choice hL order hC hG graph nodeMaps supports directed countableBound hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace q row A code extra extraGround extraSubset extraSmall
  exact ⟨X, extraBound U (ZFSet.mem_pair.2 (Or.inl rfl)),
    extraBound V (ZFSet.mem_pair.2 (Or.inr rfl)), rowBound, dataBound⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment




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

theorem binaryRowStructural_aligned_rectangle_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L)
    (meetComm : ∀ x y : L, meet x y = meet y x)
    (meetLeft : ∀ x y : L, meet x y ≤ x)
    (meetRight : ∀ x y : L, meet x y ≤ y)
    (meetGreatest : ∀ x y z : L, z ≤ x → z ≤ y → z ≤ meet x y)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
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
    let I := refinementDataHistoryIndices stages packed
    let anchors := refinementIndexFieldGraph I s.carrier 2
    let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace
    ∀ (p q : SetMembers upperQ) (r oldRow : SetMembers c.carrier) (A oldA : ZFSet.{u})
      (g1 g2 h1 h2 : G) (D X V W : L),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA →
      StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
      q ≤ upperAct.iso g1 p → q ≤ upperAct.iso g2 p →
      (∀ i : L, s.encode i ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i ≤ D) →
      (∀ i : L, s.encode i ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw oldRow) → i ≤ X) →
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
      (∀ z ∈ oldA, ZFSet.pair z (s.encode X) ∈
        stageOneDataBounds oldA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
      g1⁻¹ * h1 ∈ a.principalFix V → g2⁻¹ * h2 ∈ a.principalFix V →
      h1⁻¹ * h2 ∈ a.principalFix W →
      meet (a.iso h1 D) X = a.iso h1 V →
      meet (a.iso h2 D) X = a.iso h2 V →
      meet (a.iso h1 D) (a.iso h2 D) = a.iso h1 W →
      (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
        let hAlpha := M.transitive hs member
        let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
        let subset := (And.left stagesOrdinal) alpha member
        let lowerPacked := graphRestriction alpha packed
        let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
        letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
        let lower := SetMembers.presentation Q
        let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
          pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
          nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
          topMem topRows hh trace hAlpha cutOrdinal subset
        ∀ (H : ConditionFilter (SetMembers Q)),
          H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
          ∀ (v w : L) (x y : (M.nameDomain lower).names),
            a.principalFix v ≤ localAct.stabilizer lower x.val →
            a.principalFix w ≤ localAct.stabilizer lower y.val →
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
            Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
            ∃ tau : (M.nameDomain lower).names,
              HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
              a.principalFix (meet v w) ≤ localAct.stabilizer lower tau.val ∧
              Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
      let movedA1 := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h1) A
      let movedA2 := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h2) A
      ∃ row : SetMembers c.carrier, ∃ result : SetMembers upperQ,
        SetMembers.raw row = (SetMembers.raw oldRow ∪ SetMembers.raw (act.iso h1 r)) ∪
          SetMembers.raw (act.iso h2 r) ∧
        SetMembers.raw result = ZFSet.pair (c.encode row) (movedA2 ∪ (movedA1 ∪ oldA)) ∧
        result ≤ q ∧ result ≤ upperAct.iso h1 p ∧ result ≤ upperAct.iso h2 p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace coordinates two carrier forcingOrder
    forcingAction omega topMem topRows packed I anchors upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro upperAct p q r oldRow A oldA g1 g2 h1 h2 D X V W pCode qCode prepared below1 below2
    usedD usedX dataD dataX relative1 relative2 between overlap1 overlap2 overlap12 descent movedA1 movedA2
  have source : ZFSet.pair (c.encode r) A ∈ upperQ := pCode ▸ SetMembers.raw_mem p
  have oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ := qCode ▸ SetMembers.raw_mem q
  have reference1 := M.semanticStructuralOrder_action_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hs hh stagesOrdinal trace g1 p q r oldRow A oldA pCode qCode below1
  have reference2 := M.semanticStructuralOrder_action_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hs hh stagesOrdinal trace g2 p q r oldRow A oldA pCode qCode below2
  have agree (g h : G) (B : L) (relative : g⁻¹ * h ∈ a.principalFix B)
      (i : L) (hi : i ≤ B) : a.iso h i = a.iso g i := by
    have moved := congrArg (a.iso g) (relative i hi)
    simpa only [a.mul, a.point_inv_right] using moved
  obtain ⟨row, rowCode, rowBelowOld, rowBelowH1, rowBelowH2⟩ :=
    M.internalRowAction_rectangle_union a s b C pairing unions powers separation infinite hL hC hG graph
      choice r oldRow D X V W g1 g2 h1 h2
      (fun i hi => usedD i.val hi) (fun i hi => usedX i.val hi) reference1.1 reference2.1
      (agree g1 h1 V relative1) (agree g2 h2 V relative2)
      (fun i hi => (agree h1 h2 W between i hi).symm)
      (fun i hi hx => overlap1 ▸ meetGreatest _ _ i hi hx)
      (fun i hi hx => overlap2 ▸ meetGreatest _ _ i hi hx)
      (fun i hi hj => overlap12 ▸ meetGreatest _ _ i hi hj)
  have candidate := (M.mem_refinementHistoryForcing c.carrier lifted stages packed
    (ZFSet.pair (c.encode r) A)).1 source |>.1
  have hA : A ∈ M.sets := ((M.mem_groundSmallSubsets _ _ A).1 (ZFSet.pair_mem_prod.1 candidate).2).1
  have transported1 := M.binaryRowStructuralAssignmentImage_dataBound a s b C pairing unions powers
    separation collection infinite hL order hC hG graph nodeMaps supports directed hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace h1 D A hA dataD
  have transported2 := M.binaryRowStructuralAssignmentImage_dataBound a s b C pairing unions powers
    separation collection infinite hL order hC hG graph nodeMaps supports directed hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace h2 D A hA dataD
  have unionFacts := M.semanticStructuralTrace_aligned_rectangle_union c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace infinite choice small meet I S mu s.nonbottom.carrier tuples
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun D f _ tau entry bound => M.liftedRowTuple_supported a s b C pairing unions powers separation
      infinite hL hC hG graph hmu muOrdinal valid f tau D entry bound.2)
    r oldRow row A oldA g1 g2 h1 h2 D X V W source oldSource (pCode ▸ prepared)
    rowBelowOld reference1.1 reference2.1 rowBelowH1 rowBelowH2 reference1.2 reference2.2
    relative1 relative2 between overlap1 overlap2 overlap12 meetComm meetLeft meetRight meetGreatest
    transported1.2.2 transported2.2.2 dataX descent
  let result : SetMembers upperQ := SetMembers.ofMem _ unionFacts.1
  have resultCode : SetMembers.raw result = ZFSet.pair (c.encode row) (movedA2 ∪ (movedA1 ∪ oldA)) :=
    SetMembers.raw_ofMem _ _
  have movedCode (h : G) := M.semanticStructuralAction_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace h p r A pCode
  refine ⟨row, result, rowCode, resultCode, ?_, ?_, ?_⟩
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw q) ∈ _
    rw [resultCode, qCode]
    exact unionFacts.2.1
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw (upperAct.iso h1 p)) ∈ _
    rw [resultCode, movedCode h1]
    exact unionFacts.2.2.1
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw (upperAct.iso h2 p)) ∈ _
    rw [resultCode, movedCode h2]
    exact unionFacts.2.2.2

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

theorem structural_rectangle_union
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
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
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  ∀ (p q : SetMembers upperQ) (r oldRow : SetMembers c.carrier) (A oldA : ZFSet.{u})
    (g1 g2 : SetMembers geometry.actors) (dBound X V W : SetMembers geometry.carrier),
    SetMembers.raw p = ZFSet.pair (c.encode r) A →
    SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
    q ≤ upperAct.iso g1 p → q ≤ upperAct.iso g2 p →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw r) → i ≤ dBound) →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw oldRow) → i ≤ X) →
    (∀ z ∈ A, ZFSet.pair z (s.encode dBound) ∈
      stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    (∀ z ∈ oldA, ZFSet.pair z (s.encode X) ∈
      stageOneDataBounds oldA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    ExternalRectangleCode geometry.carrier geometry.actors geometry.order geometry.meetGraph geometry.action
      (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw dBound)
      (SetMembers.raw g1) (SetMembers.raw g2) →
    a.iso g1 dBound ≤ X → a.iso g2 dBound ≤ X →
    (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∃ h1 h2 : SetMembers geometry.actors,
      RectangleAtBoundCode geometry.carrier geometry.order geometry.meetGraph geometry.action
        (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw dBound)
        (SetMembers.raw g1) (SetMembers.raw g2) (SetMembers.raw X)
        (SetMembers.raw h1) (SetMembers.raw h2) ∧
    (let movedA1 := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h1) A;
    let movedA2 := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h2) A;
    ∃ row : SetMembers c.carrier, ∃ result : SetMembers upperQ,
      SetMembers.raw row = (SetMembers.raw oldRow ∪ SetMembers.raw (act.iso h1 r)) ∪
        SetMembers.raw (act.iso h2 r) ∧
      SetMembers.raw result = ZFSet.pair (c.encode row) (movedA2 ∪ (movedA1 ∪ oldA)) ∧
      result ≤ q ∧ result ≤ upperAct.iso h1 p ∧ result ≤ upperAct.iso h2 p) := by
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  intro p q r oldRow A oldA g1 g2 dBound X V W pCode qCode prepared below1 below2
    usedD usedX dataD dataX request bound1 bound2 descent
  have meetComm (x y : SetMembers geometry.carrier) :
      geometry.meet.smallMeet x y = geometry.meet.smallMeet y x := by
    apply le_antisymm
    · exact geometry.meet.toSmallMeetOrder.le_meet
        (geometry.meet.toSmallMeetOrder.meet_le_right _ _) (geometry.meet.toSmallMeetOrder.meet_le_left _ _)
    · exact geometry.meet.toSmallMeetOrder.le_meet
        (geometry.meet.toSmallMeetOrder.meet_le_right _ _) (geometry.meet.toSmallMeetOrder.meet_le_left _ _)
  obtain ⟨h1, h2, rectangle, relative1, relative2, between, overlap1, overlap2, overlap12⟩ :=
    fulfilled.decoded_rectangle_action_data V W dBound X g1 g2 request bound1 bound2
  refine ⟨h1, h2, rectangle, ?_⟩
  exact M.binaryRowStructural_aligned_rectangle_union a s b columns pairing unions powers separation
    collection infinite hL order hC hG graph nodeMaps supports directed choice small geometry.meet.smallMeet
    meetComm geometry.meet.toSmallMeetOrder.meet_le_left geometry.meet.toSmallMeetOrder.meet_le_right
    (fun _ _ _ left right => geometry.meet.toSmallMeetOrder.le_meet left right) hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace p q r oldRow A oldA g1 g2 h1 h2 dBound X V W pCode qCode prepared below1 below2
    usedD usedX dataD dataX relative1 relative2 between overlap1 overlap2 overlap12 descent






theorem structural_rectangle_refinement
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
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
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (p : SetMembers upperQ) (sourceRow : SetMembers c.carrier) (A : ZFSet.{u})
    (dBound V W : SetMembers geometry.carrier) (x y : Name upper),
    SetMembers.raw p = ZFSet.pair (c.encode sourceRow) A →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw sourceRow) → i ≤ dBound) →
    (∀ z ∈ A, ZFSet.pair z (s.encode dBound) ∈
      stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    V ≤ dBound → W ≤ dBound →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∀ (g1 g2 : SetMembers geometry.actors),
      g1 ∈ a.principalFix (geometry.meet.smallMeet V W) →
      g2 ∈ a.principalFix (geometry.meet.smallMeet V W) →
      geometry.meet.smallMeet (a.iso g1 dBound) (a.iso g2 dBound) = geometry.meet.smallMeet V W →
      ∀ r, r ≤ upperAct.iso g1 p → r ≤ upperAct.iso g2 p →
        DenseBelow r (upperAct.RectangleWitness upper p x y g1 g2) := by
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  intro p sourceRow A dBound V W x y pCode prepared usedD dataD vd wd sx sy descent
    g1 g2 fixed1 fixed2 separated r ref1 ref2 q qr
  obtain ⟨rawRow, rowMem, oldA, _, qCodeRaw⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier lifted stages packed (SetMembers.raw_mem q))
  let oldRow := SetMembers.ofMem rawRow rowMem
  have qCode : SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA := by
    exact qCodeRaw.trans (congrArg (fun z => ZFSet.pair z oldA)
      (SetMembers.raw_ofMem rawRow rowMem).symm)
  obtain ⟨X, upper1, upper2, usedX, dataX⟩ := fulfilled.structural_bounds_with
    collection infinite choice columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    q oldRow oldA (a.iso g1 dBound) (a.iso g2 dBound) qCode
  have request := geometry.decoded_rectangle_request V W dBound g1 g2 vd wd fixed1 fixed2 separated
  obtain ⟨h1, h2, rectangle, _row, result, _rowCode, _resultCode, belowQ, below1, below2⟩ :=
    fulfilled.structural_rectangle_union collection infinite choice small columns hColumns
      hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace p q sourceRow oldRow A oldA g1 g2 dBound X V W
      pCode qCode prepared (le_trans qr ref1) (le_trans qr ref2) usedD usedX dataD dataX
      request upper1 upper2 descent
  have agree (g h : SetMembers geometry.actors) (v : SetMembers geometry.carrier)
      (rawAgree : ActionAgreementBelow geometry.carrier geometry.order geometry.action
        (SetMembers.raw g) (SetMembers.raw h) (SetMembers.raw v)) :
      ∀ i, i ≤ v → a.iso g i = a.iso h i := by
    intro i lower
    apply SetMembers.raw_injective
    exact rawAgree.entry_eq geometry.action_code (SetMembers.raw_mem h) (SetMembers.raw_mem i)
      lower (geometry.action_code.act_mem g i) (geometry.action_code.act_mem h i)
  let geom := geometry.action_code.toOrderAction geometry.group_code geometry.meet
  exact ⟨result, belowQ, h1, h2, below1, below2,
    upperAct.act_eq_of_support_agreement geom upper sx (agree h1 g1 V rectangle.first_agreement),
    upperAct.act_eq_of_support_agreement geom upper sx (agree h2 g2 V rectangle.second_agreement),
    upperAct.act_eq_of_support_agreement geom upper sy (agree h1 h2 W rectangle.common_agreement)⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
