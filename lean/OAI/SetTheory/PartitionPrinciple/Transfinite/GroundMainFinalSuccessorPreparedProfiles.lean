import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalPreparedInsertionProfiles

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

theorem successor_prepared_insertion_profiles
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
      let localValid := M.refinementHistoryRowNameFamily_valid c
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) (graphRestriction (insert alpha alpha) packed) →
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      ∀ r0 : SetMembers Q,
      let J := M.fixedIndexAugmentedRequests localAct lower s a alpha lifted squared localValid idx A Rc.val u.val
      let N := M.niceSupportNameCodes localAct lower lifted a.principalFix
      let Profiles (k : ZFSet.{u}) := M.certificateProfileImage J s.carrier N k
      let prefixIndices := refinementDataHistoryIndices alpha lowerPacked
      let prefixAnchors := refinementIndexFieldGraph prefixIndices s.carrier 2
      let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
      J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
      ∃ k ∈ M.sets, ZFSet.IsFunc J (M.supportedEqualityCertificateBound s.carrier N) k ∧
        Profiles k ∈ M.sets ∧ M.groundEmbeddable (Profiles k) ZFSet.omega ∧
        (∀ F ∈ Profiles k, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
      ∃ Pb basis representatives,
        ZFSet.pair (Name.refinementClass lifted localValid Rc.val u.val).val
          (ZFSet.pair Pb (ZFSet.pair basis representatives)) ∈ k ∧ Pb ∈ Profiles k ∧
      ∃ generators ∈ M.sets, M.groundEmbeddable generators ZFSet.omega ∧ generators.Nonempty ∧
        generators ⊆ testedMeetFilter Pb geometry.order (s.encode E) ∧
        M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators =
          testedMeetFilter Pb geometry.order (s.encode E) ∧
      ∃ r : SetMembers Q, r ≤ r0 ∧
      ∃ (rowR : SetMembers c.carrier) (lowerA : ZFSet.{u}),
        lower.encode r = ZFSet.pair (c.encode rowR) lowerA ∧
        StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier (lower.encode r) ∧
      ∃ D0 : SetMembers geometry.carrier, E ≤ D0 ∧
        a.principalFix D0 ≤ localAct.stabilizer lower u.val ∧
        (∀ i : SetMembers geometry.carrier, s.encode i ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw rowR) → i ≤ D0) ∧
        (∀ z ∈ lowerA, ZFSet.pair z (s.encode D0) ∈
          stageOneDataBounds lowerA prefixIndices lifted S s.carrier mu s.nonbottom.carrier
            s.conditionOrder prefixAnchors tuples) ∧
        M.DecidesVisibilityProfile localAct lower s a.principalFix lifted Pb
          (Name.refinementClass lifted localValid Rc.val u.val) r ∧
        (∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
          ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
          F ∈ Profiles k ∧ M.DecidesVisibilityProfile localAct lower s a.principalFix lifted F z.val r) ∧
        ∀ v w : (M.nameDomain lower).names, v.val.val ∈ lifted → w.val.val ∈ lifted →
          stageOneAssignment idx v.val.val w.val.val ∈ A →
          ∃ F B f, ZFSet.pair (Name.refinementClass lifted localValid Rf.val w.val).val
            (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ F ∈ Profiles k ∧
            M.DecidesVisibilityProfile localAct lower s a.principalFix lifted F
              (Name.refinementClass lifted localValid Rf.val w.val) r := by
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
  let localValid := M.refinementHistoryRowNameFamily_valid c
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier lifted valid1
  let gamma := insert alpha alpha
  have hGamma : gamma ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have gammaOrdinal : ordinalSetProperty gamma := ordinalSetProperty_succ cutOrdinal
  have alphaGamma : alpha ⊆ gamma := fun _ hx => ZFSet.mem_insert_of_mem _ hx
  have gammaSubset : gamma ⊆ stages := by
    intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact member
    · exact subset x old
  let historyGamma := graphRestriction gamma history
  have hhGamma : historyGamma ∈ M.sets := M.graphRestriction_mem unions separation hGamma hh
  have traceGamma := trace.restrict gammaOrdinal gammaSubset
  let packedGamma := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared gamma historyGamma
  have packedGammaEq : packedGamma = graphRestriction gamma packed :=
    (M.structuralRefinementHistory_history_restrict b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared gamma history).trans
      (M.structuralRefinementHistory_domain_restrict b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared gammaSubset)
  have lowerPackedEq : graphRestriction alpha packedGamma = lowerPacked := by
    rw [packedGammaEq, graphRestriction_restrict alphaGamma]
  let Property : ∀ (domainSet : ZFSet.{u}) (orderQ : PartialOrder (SetMembers domainSet)),
      @PosetAction (SetMembers geometry.actors) _ (SetMembers domainSet) orderQ → Prop :=
    fun domainSet orderQ actionQ =>
      letI := orderQ
      ∀ topQ : OrderTop (SetMembers domainSet),
      letI := topQ
      let lower := SetMembers.presentation domainSet
      ∀ localValid : ∀ z ∈ lifted, IsName lower z,
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted (insert alpha alpha) (graphRestriction (insert alpha alpha) packed) →
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices actionQ lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      ∀ r0 : SetMembers domainSet,
      let J := M.fixedIndexAugmentedRequests actionQ lower s a alpha lifted squared localValid idx A Rc.val u.val
      let N := M.niceSupportNameCodes actionQ lower lifted a.principalFix
      let Profiles (k : ZFSet.{u}) := M.certificateProfileImage J s.carrier N k
      let prefixIndices := refinementDataHistoryIndices alpha lowerPacked
      let prefixAnchors := refinementIndexFieldGraph prefixIndices s.carrier 2
      let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
      J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
      ∃ k ∈ M.sets, ZFSet.IsFunc J (M.supportedEqualityCertificateBound s.carrier N) k ∧
        Profiles k ∈ M.sets ∧ M.groundEmbeddable (Profiles k) ZFSet.omega ∧
        (∀ F ∈ Profiles k, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
      ∃ Pb basis representatives,
        ZFSet.pair (Name.refinementClass lifted localValid Rc.val u.val).val
          (ZFSet.pair Pb (ZFSet.pair basis representatives)) ∈ k ∧ Pb ∈ Profiles k ∧
      ∃ generators ∈ M.sets, M.groundEmbeddable generators ZFSet.omega ∧ generators.Nonempty ∧
        generators ⊆ testedMeetFilter Pb geometry.order (s.encode E) ∧
        M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators =
          testedMeetFilter Pb geometry.order (s.encode E) ∧
      ∃ r : SetMembers domainSet, r ≤ r0 ∧
      ∃ (rowR : SetMembers c.carrier) (lowerA : ZFSet.{u}),
        lower.encode r = ZFSet.pair (c.encode rowR) lowerA ∧
        StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier (lower.encode r) ∧
      ∃ D0 : SetMembers geometry.carrier, E ≤ D0 ∧
        a.principalFix D0 ≤ actionQ.stabilizer lower u.val ∧
        (∀ i : SetMembers geometry.carrier, s.encode i ∈
          rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw rowR) → i ≤ D0) ∧
        (∀ z ∈ lowerA, ZFSet.pair z (s.encode D0) ∈
          stageOneDataBounds lowerA prefixIndices lifted S s.carrier mu s.nonbottom.carrier
            s.conditionOrder prefixAnchors tuples) ∧
        M.DecidesVisibilityProfile actionQ lower s a.principalFix lifted Pb
          (Name.refinementClass lifted localValid Rc.val u.val) r ∧
        (∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
          ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
          F ∈ Profiles k ∧ M.DecidesVisibilityProfile actionQ lower s a.principalFix lifted F z.val r) ∧
        ∀ v w : (M.nameDomain lower).names, v.val.val ∈ lifted → w.val.val ∈ lifted →
          stageOneAssignment idx v.val.val w.val.val ∈ A →
          ∃ F B f, ZFSet.pair (Name.refinementClass lifted localValid Rf.val w.val).val
            (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ F ∈ Profiles k ∧
            M.DecidesVisibilityProfile actionQ lower s a.principalFix lifted F
              (Name.refinementClass lifted localValid Rf.val w.val) r
  let QGamma := M.refinementHistoryForcing c.carrier lifted alpha (graphRestriction alpha packedGamma)
  let gammaOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha
    (graphRestriction alpha packedGamma)
  let runGamma := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared gammaOrdinal traceGamma
  let topGamma := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha
    (graphRestriction alpha packedGamma) (runGamma.carriers.restrict cutOrdinal alphaGamma)
    cutOrdinal carrier (c.encode ⊤) topMem topRows
  let validGamma := M.refinementHistoryRowNameFamily_valid c
    (runGamma.carriers.restrict cutOrdinal alphaGamma) cutOrdinal carrier lifted valid1
  let actionGamma := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hhGamma traceGamma hAlpha cutOrdinal alphaGamma
  have inside : Property QGamma gammaOrder actionGamma := by
    intro topQ
    have topEq : topQ = topGamma := Subsingleton.elim _ _
    subst topQ
    dsimp only
    intro validQ
    have validEq : validQ = validGamma := Subsingleton.elim _ _
    subst validQ
    intro row A condition V E U Rf Rc u inI hu r0
    have conditionGamma : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted gamma packedGamma := by
      rw [packedGammaEq]
      exact condition
    obtain ⟨hJ, smallJ, k, hk, function, profilesGround, profilesSmall, filters,
      Pb, basis, representatives, coarseEdge, coarseMember, generators, hGenerators,
      smallGenerators, nonemptyGenerators, generatorsSubset, generated, r, below,
      rowR, lowerA, rCode, prepared, D0, eBelow, nameSupport, rowBound, dataBound,
      coarseDecision, decisions, oldProfiles⟩ :=
      fulfilled.prepared_augmented_profiles collection infinite choice small smallD irreflexive
        columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
        children1 children2 gamma historyGamma hGamma hhGamma gammaOrdinal traceGamma
        alpha (ZFSet.mem_insert _ _) row A conditionGamma V E U Rf Rc u inI hu r0
    have preparedParent : StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier
        ((SetMembers.presentation QGamma).encode r) := by
      have transfer (raw : ZFSet.{u}) :
          StoredPreparedConditionCode M c.carrier lifted alpha (graphRestriction alpha packedGamma) s.carrier raw →
          StoredPreparedConditionCode M c.carrier lifted alpha lowerPacked s.carrier raw := by
        rw [lowerPackedEq]
        exact id
      exact transfer _ prepared
    rw [lowerPackedEq] at dataBound
    exact ⟨hJ, smallJ, k, hk, function, profilesGround, profilesSmall, filters,
      Pb, basis, representatives, coarseEdge, coarseMember, generators, hGenerators,
      smallGenerators, nonemptyGenerators, generatorsSubset, generated, r, below,
      rowR, lowerA, rCode, preparedParent, D0, eBelow, nameSupport, rowBound, dataBound,
      coarseDecision, decisions, oldProfiles⟩
  have outside := (M.semanticStructuralPrefixAction_subhistory_property c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hAlpha cutOrdinal subset hGamma gammaOrdinal alphaGamma gammaSubset Property).1 inside
  exact outside inferInstance localValid

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
