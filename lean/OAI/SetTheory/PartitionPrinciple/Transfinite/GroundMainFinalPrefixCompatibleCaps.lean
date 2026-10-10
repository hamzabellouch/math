import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalStructuralLateProfileExclusions

namespace OAI

open scoped ZFSet



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

theorem structural_prefix_compatible_caps
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable)
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
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
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
      let indices := refinementDataHistoryIndices alpha lowerPacked
      let anchors := refinementIndexFieldGraph indices s.carrier 2
      ∀ (r : SetMembers Q) (row : SetMembers c.carrier) (A : ZFSet.{u}),
        lower.encode r = ZFSet.pair (c.encode row) A →
        StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier (lower.encode r) →
      ∀ (V E D0 : SetMembers geometry.carrier) (B Pb Profiles : ZFSet.{u}),
        V < E → V ≤ D0 →
        MeetFilterCode geometry.carrier geometry.order geometry.meetGraph Pb →
        B ∈ M.sets → B.Nonempty → B ⊆ testedMeetFilter Pb geometry.order (s.encode E) →
        M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph B =
          testedMeetFilter Pb geometry.order (s.encode E) →
        Profiles ∈ M.sets → M.groundEmbeddable Profiles ZFSet.omega →
        (∀ profile ∈ Profiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph profile) →
        (∀ i : SetMembers geometry.carrier, s.encode i ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) → i ≤ D0) →
        (∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈ stageOneDataBounds A indices lifted S s.carrier mu
          s.nonbottom.carrier s.conditionOrder anchors tuples) →
      ∃ (g : SetMembers geometry.actors) (cap : SetMembers geometry.carrier) (q : SetMembers Q),
        q ≤ r ∧ q ≤ localAct.iso g r ∧ g ∈ a.principalFix V ∧ V < cap ∧ ¬ E ≤ cap ∧
        a.iso g D0 ≤ cap ∧
        (∀ v : SetMembers geometry.carrier,
          s.encode v ∈ testedMeetFilter Pb s.conditionOrder (s.encode E) → cap ≤ v) ∧
        (∀ v : SetMembers geometry.carrier, E ≤ v →
          s.encode v ∉ testedMeetFilter Pb s.conditionOrder (s.encode E) → geometry.meet.smallMeet cap v = V) ∧
        (∀ profile ∈ Profiles, s.encode V ∉ profile → s.encode cap ∉ profile) ∧
        let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) lifted squared alpha history (b.encode g) A
        ∃ commonRow : SetMembers c.carrier,
          SetMembers.raw commonRow = SetMembers.raw row ∪ SetMembers.raw (act.iso g row) ∧
          lower.encode q = ZFSet.pair (c.encode commonRow) (A ∪ movedA) := by
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
  intro alpha member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
  let subset := (And.left stagesOrdinal) alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  let lower := SetMembers.presentation Q
  let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let indices := refinementDataHistoryIndices alpha lowerPacked
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro r row A rCode prepared V E D0 B Pb Profiles strict bound filter hB nonempty contained
    generated hProfiles smallProfiles profileFilters rowD dataD
  have packedEq := (M.structuralRefinementHistory_history_restrict b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared alpha history).trans
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared subset)
  have inNodes : B ⊆ geometry.carrier := fun z hz =>
    filter.subset ((mem_testedMeetFilter Pb geometry.order (s.encode E) z).1 (contained hz)).1
  have above : ∀ z ∈ B, ZFSet.pair (s.encode E) z ∈ geometry.order := fun z hz =>
    ((mem_testedMeetFilter Pb geometry.order (s.encode E) z).1 (contained hz)).2
  have condition : ZFSet.pair (c.encode row) A ∈ Q := rCode ▸ SetMembers.raw_mem r
  obtain ⟨filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, badComp, hBadComp, badCompSubset, badCompSmall, bad, hBad, badSubset, badSmall,
    includesComp, goodProfiles, survivor, compatible⟩ :=
    fulfilled.structural_compatible_insertion_with_late_profiles collection infinite choice labels small
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      alpha (graphRestriction alpha history) hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
      cutOrdinal (trace.restrict cutOrdinal subset) row A
      (by
        change ZFSet.pair (c.encode row) A ∈ M.refinementHistoryForcing c.carrier lifted alpha
          (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
            (supportBasisCode s b a.principalFix) lifted squared alpha (graphRestriction alpha history))
        rw [packedEq]
        exact condition)
      (by
        change StoredPreparedConditionCode M c.carrier lifted alpha
          (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
            (supportBasisCode s b a.principalFix) lifted squared alpha (graphRestriction alpha history))
          s.carrier (ZFSet.pair (c.encode row) A)
        rw [packedEq]
        exact rCode ▸ prepared)
      V E D0 B Profiles strict bound hB inNodes nonempty above hProfiles smallProfiles profileFilters rowD
      (by
        let restrictedPacked := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
          (supportBasisCode s b a.principalFix) lifted squared alpha (graphRestriction alpha history)
        change ∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈ stageOneDataBounds A
          (refinementDataHistoryIndices alpha restrictedPacked) lifted S s.carrier mu
          s.nonbottom.carrier s.conditionOrder
          (refinementIndexFieldGraph (refinementDataHistoryIndices alpha restrictedPacked) s.carrier 2) tuples
        dsimp only [restrictedPacked]
        rw [packedEq]
        exact dataD)
  obtain ⟨label, outside⟩ := survivor
  let g := family.decodedActors label
  let cap := family.decodedCaps label
  have capEdge := family.decodedCaps_entry label
  obtain ⟨fixed, strictCap, notAbove, movedBound, tested, commonRow, rowCode,
      qCondition, qBelow, qMovedBelow⟩ := compatible label outside
  rw [M.structuralAssignmentImage_history_restrict, packedEq] at qCondition qBelow qMovedBelow
  let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared alpha history (b.encode g) A
  let q : SetMembers Q := SetMembers.ofMem (ZFSet.pair (c.encode commonRow) (A ∪ movedA)) qCondition
  have qCode : lower.encode q = ZFSet.pair (c.encode commonRow) (A ∪ movedA) :=
    SetMembers.raw_ofMem _ _
  have actedCode := M.semanticStructuralPrefixAction_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset g r row A rCode
  have leR : q ≤ r := by
    change ZFSet.pair (lower.encode q) (lower.encode r) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder lifted alpha lowerPacked
    rw [qCode, rCode]
    exact qBelow
  have leMoved : q ≤ localAct.iso g r := by
    change ZFSet.pair (lower.encode q) (SetMembers.raw (localAct.iso g r)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder lifted alpha lowerPacked
    rw [qCode, actedCode]
    exact qMovedBelow
  refine ⟨g, cap, q, leR, leMoved, fixed, strictCap, notAbove, movedBound, ?_, ?_, ?_,
    commonRow, rowCode, qCode⟩
  · intro v member
    rw [geometry.decoded_order_eq] at member
    have ev : E ≤ v := ((mem_testedMeetFilter Pb geometry.order (s.encode E) (s.encode v)).1 member).2
    apply (tested v ev).1
    rwa [generated]
  · intro v ev absent
    rw [geometry.decoded_order_eq] at absent
    apply (geometry.meet.smallMeet_eq_iff cap v V).2
    apply (tested v ev).2
    rwa [generated]
  · exact goodProfiles _ _ capEdge outside

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
