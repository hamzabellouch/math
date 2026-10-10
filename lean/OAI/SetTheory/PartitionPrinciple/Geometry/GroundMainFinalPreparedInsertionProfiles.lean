import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalPreparedPrefixBounds

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

theorem augmented_profile_family
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
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted stages packed →
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc u : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid → u.val.val ∈ lifted →
      ∀ p : SetMembers Q,
      let J := M.fixedIndexAugmentedRequests localAct lower s a alpha lifted squared localValid idx A Rc.val u.val
      let N := M.niceSupportNameCodes localAct lower lifted a.principalFix
      J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
      ∃ (validJ : ∀ z ∈ J, IsName lower z) (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) ∧ H.GenericFor (formulaFamily (M.nameDomain lower)) ∧
        ∃ k ∈ M.sets, ZFSet.IsFunc J (M.supportedEqualityCertificateBound s.carrier N) k ∧
          k ⊆ M.supportedCertificateFamilyRelation localAct lower s lifted a.principalFix
            geometry.order J validJ H ∧
          ∃ q, H.mem q ∧ q ≤ p ∧
            let Profiles := M.certificateProfileImage J s.carrier N k
            Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
            (∀ F ∈ Profiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
            ∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
              ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              F ∈ Profiles ∧ B.Nonempty ∧
              M.DecidesVisibilityProfile localAct lower s a.principalFix lifted F z.val q ∧
              (∀ v ∈ B, ∀ tau : Name lower, tau.val ∈ N →
                ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) := by
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed
    alpha member hAlpha cutOrdinal subset lowerPacked Q
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  intro historyRun
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  intro lower localAct localValid row A condition V E U Rf Rc u idx inI hu p J N
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation infinite choice
    coordinates two
  obtain ⟨lowerGround, lowerOrder, maps, lowerClosed, terms, children⟩ :=
    M.semanticStructuralPrefix_preparation_inputs c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace member infinite choice rowClosed
  obtain ⟨_, _, hJ, smallJ, validJ, _, facts, _, _⟩ :=
    M.semanticStructuralPrefix_augmentedClassRequests c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace member infinite choice condition V E U Rf Rc u inI hu
  obtain ⟨H, hp, coded, ordinary, _symmetric⟩ := M.exists_joint_generic lower localAct
    (a.principalSupportFamily ⊥ directed) small lowerGround p
  have descent := fulfilled.structural_prefix_descent collection infinite choice small smallD irreflexive
    columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace alpha member H coded ordinary
  obtain ⟨k, hk, function, selected, q, hq, qp, _forced, decisions⟩ :=
    fulfilled.exists_forcedSupportedCertificateFamily lower collection infinite choice lowerGround lowerOrder
      small lowerClosed smallD irreflexive localAct maps lifted hLifted localValid terms children
      H coded ordinary descent J hJ validJ smallJ (fun z hz => (facts z hz).1)
      (fun z hz => (facts z hz).2.2.2 H) p hp
  have codesGround : N ∈ M.sets := M.niceSupportNameCodes_mem localAct lower s lifted a.principalFix b
    pairing unions powers separation collection lowerGround hG hL supports maps hLifted localValid
  obtain ⟨profilesGround, profilesSmall⟩ := M.certificateProfileImage_mem_small pairing unions powers
    separation choice hJ hL codesGround hk omega function smallJ
  refine ⟨hJ, smallJ, validJ, H, coded, ordinary, k, hk, function, selected, q, hq, qp,
    profilesGround, profilesSmall, ?_, ?_⟩
  · intro F memberF
    obtain ⟨z, B, f, entry⟩ := (M.mem_certificateProfileImage function F).1 memberF
    have hz := (ZFSet.pair_mem_prod.1 (function.1 entry)).1
    let name : (M.nameDomain lower).names := ⟨⟨z, validJ z hz⟩, M.transitive hJ hz⟩
    exact (decisions name F B f entry).2.1
  · intro z F B f entry
    have chosen := decisions z F B f entry
    exact ⟨(M.mem_certificateProfileImage function F).2 ⟨z.val.val, B, f, entry⟩,
      chosen.2.2.1, chosen.2.2.2.1, chosen.2.2.2.2.1⟩






theorem prepared_augmented_profiles
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
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier lifted stages packed →
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
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed
    alpha member hAlpha cutOrdinal subset lowerPacked Q
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
  intro historyRun
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier (c.encode ⊤) topMem topRows
  intro lower localAct localValid row A condition V E U Rf Rc u idx inI hu r0 J N
    Profiles prefixIndices prefixAnchors tuples
  obtain ⟨hJ, smallJ, validJ, H, _coded, _ordinary, k, hk, function, _selected,
      q0, _hq0, q0Below, profilesGround, profilesSmall, profileFilters, decisions⟩ :=
    fulfilled.augmented_profile_family collection infinite choice small smallD irreflexive
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace alpha member
      row A condition V E U Rf Rc u inI hu r0
  have coarseMember : (Name.refinementClass lifted localValid Rc.val u.val).val ∈ J :=
    ZFSet.mem_insert _ _
  let coarse : (M.nameDomain lower).names :=
    ⟨Name.refinementClass lifted localValid Rc.val u.val, M.transitive hJ coarseMember⟩
  obtain ⟨coarseValue, coarseEdge, _coarseUnique⟩ := function.2 coarse.val.val coarseMember
  have coarseBound := (ZFSet.pair_mem_prod.1 (function.1 coarseEdge)).2
  obtain ⟨Pb, _hPb, tail, hTail, rfl⟩ := ZFSet.mem_prod.1 coarseBound
  obtain ⟨basis, _hBasis, representatives, _hRepresentatives, rfl⟩ := ZFSet.mem_prod.1 hTail
  have coarseChosen := decisions coarse Pb basis representatives coarseEdge
  have PbGround := M.transitive profilesGround coarseChosen.1
  obtain ⟨_testedGround, _testedFilter, _testedAbove, generators, hGenerators,
      smallGenerators, nonemptyGenerators, generatorsSubset, _coinitial, generated⟩ :=
    fulfilled.tested_filter_generators infinite choice smallD irreflexive PbGround
      (profileFilters Pb coarseChosen.1) (s.encode_mem E)
  obtain ⟨r, rBelowQ0, rowR, lowerA, rCode, preparedAt, D0, eBelow, nameSupport, rowBound, dataBound⟩ :=
    fulfilled.prepared_prefix_term_bound collection infinite choice small smallD irreflexive
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace alpha member E u hu q0
  have decisionsAt : ∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
      ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      F ∈ M.certificateProfileImage J s.carrier N k ∧
        M.DecidesVisibilityProfile localAct lower s a.principalFix lifted F z.val r := by
    intro z F B f edge
    have chosen := decisions z F B f edge
    refine ⟨chosen.1, fun v => ⟨?_, ?_⟩⟩
    · intro yes
      exact Name.forcesMem_mono ((chosen.2.2.1 v).1 yes) rBelowQ0
    · intro no p pr
      exact (chosen.2.2.1 v).2 no p (pr.trans rBelowQ0)
  refine ⟨hJ, smallJ, k, hk, function, profilesGround, profilesSmall, profileFilters,
    Pb, basis, representatives, coarseEdge, coarseChosen.1, generators, hGenerators,
    smallGenerators, nonemptyGenerators, generatorsSubset, generated, r, rBelowQ0.trans q0Below,
    rowR, lowerA, rCode, preparedAt, D0, eBelow, nameSupport, rowBound, dataBound,
    (decisionsAt coarse Pb basis representatives coarseEdge).2, decisionsAt, ?_⟩
  intro v w hv hw old
  obtain ⟨_, _, _, _, _, _, _, _, exactJ⟩ :=
    M.semanticStructuralPrefix_augmentedClassRequests c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace member infinite choice condition V E U Rf Rc u inI hu
  have fineMember : (Name.refinementClass lifted localValid Rf.val w.val).val ∈ J :=
    (exactJ _).2 (Or.inr ⟨v.val, w.val, hv, hw, old, rfl⟩)
  let fine : (M.nameDomain lower).names :=
    ⟨Name.refinementClass lifted localValid Rf.val w.val, M.transitive hJ fineMember⟩
  obtain ⟨value, edge, _unique⟩ := function.2 fine.val.val fineMember
  have bound := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
  obtain ⟨F, _hF, tail, hTail, rfl⟩ := ZFSet.mem_prod.1 bound
  obtain ⟨B, _hB, f, _hf, rfl⟩ := ZFSet.mem_prod.1 hTail
  exact ⟨F, B, f, edge, decisionsAt fine F B f edge⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
