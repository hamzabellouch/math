import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalPersistentAssignmentLabels

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

theorem structural_persistent_successor_label_injection
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
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
      let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
        historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
      let upper := SetMembers.presentation upperSet
      let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
        ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
          lifted, squared, stages, history]
        (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
          (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
      let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hs hh stagesOrdinal trace
      let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared stages history
        pairing unions powers separation collection hG hL supports hh hLifted witnesses
      let inc := RecursiveRefinementOrderHistory.inclusionFunction historyRun stagesOrdinal cutOrdinal subset
        pairing unions powers separation infinite choice hs hPacked hLifted hAlpha carrier (c.encode ⊤)
        topMem topRows mono
      ∀ (V E : SetMembers geometry.carrier) (U Rf Rc : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices localAct lower s a alpha lifted squared localValid →
      let gamma := insert alpha alpha
      let hGamma := M.insert_mem pairing unions hAlpha hAlpha
      let gammaOrdinal := ordinalSetProperty_succ cutOrdinal
      let alphaGamma : alpha ⊆ gamma := fun x hx => ZFSet.mem_insert_of_mem alpha hx
      let gammaSubset : gamma ⊆ stages := fun x hx =>
        Or.elim (Iff.mp ZFSet.mem_insert_iff hx)
          (fun equal => Eq.mpr (congrArg (fun z => z ∈ stages) equal) member)
          (fun old => subset x old)
      let gammaPacked := graphRestriction gamma packed
      let gammaPackedGround := M.graphRestriction_mem unions separation hGamma hPacked
      let gammaRun := historyRun.restrict gammaOrdinal gammaSubset
      let middleSet := M.refinementHistoryForcing c.carrier lifted gamma gammaPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted gamma gammaPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted gamma gammaPacked
        gammaRun.carriers gammaOrdinal carrier (c.encode ⊤) topMem topRows
      let middle := SetMembers.presentation middleSet
      let gammaMono := fun level fields (entry : ZFSet.pair level (refinementFormulaDataCode fields) ∈ gammaPacked) => mono level fields
        (And.left (Iff.mp pair_mem_graphRestriction entry))
      let nestedInclude := RecursiveRefinementOrderHistory.inclusionFunction gammaRun gammaOrdinal cutOrdinal alphaGamma
        pairing unions powers separation infinite choice hGamma gammaPackedGround hLifted hAlpha carrier
        (c.encode ⊤) topMem topRows gammaMono
      let toNested := fun x : SetMembers Q => SetMembers.ofMem (SetMembers.raw x)
        (Eq.mpr (congrArg (fun h => SetMembers.raw x ∈ M.refinementHistoryForcing c.carrier lifted alpha h)
          (graphRestriction_restrict alphaGamma)) (SetMembers.raw_mem x))
      let prefixInclude := fun x : SetMembers Q => nestedInclude (toNested x)
      let successorLabel := Name.refinementAssignmentLabel middle prefixInclude ⊤ lifted localValid idx Rf.val Rc.val
      let middleAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hGamma gammaOrdinal gammaSubset
      let lift := M.semanticStructuralNameLift c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hs hh stagesOrdinal trace hGamma gammaOrdinal gammaSubset infinite choice
      let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hs hh stagesOrdinal trace
      successorLabel.val ∈ M.sets ∧
        a.principalFix E ≤ middleAct.stabilizer middle successorLabel ∧
        HereditarilySymmetric middleAct middle (a.principalSupportFamily ⊥ directed) successorLabel ∧
        (lift successorLabel).val = successorLabel.val ∧
        (lift successorLabel).val ∈ M.sets ∧
        a.principalFix E ≤ upperAct.stabilizer upper (lift successorLabel) ∧
        HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) (lift successorLabel) ∧
        ∀ H : ConditionFilter (SetMembers upperSet), H.GenericFor (formulaFamily (M.nameDomain upper)) →
        let J := Name.eval {p | H.mem p} (lift successorLabel)
        let coarse := Name.eval {q | H.mem (inc q)} (Name.refinementQuotient lifted localValid U.val Rc.val)
        let fine := Name.eval {q | H.mem (inc q)} (Name.refinementQuotient lifted localValid U.val Rf.val)
        Name.eval {p | H.mem p} (Name.refinementAssignmentLabel upper inc ⊤ lifted localValid idx Rf.val Rc.val) = J ∧
        InjectionCode coarse fine J ∧
        J ∈ (M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H).sets := by
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
  let upperSet := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upper := SetMembers.presentation upperSet
  let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared stages history
    pairing unions powers separation collection hG hL supports hh hLifted witnesses
  let inc := RecursiveRefinementOrderHistory.inclusionFunction historyRun stagesOrdinal cutOrdinal subset
    pairing unions powers separation infinite choice hs hPacked hLifted hAlpha carrier (c.encode ⊤)
    topMem topRows mono
  intro V E U Rf Rc index
  let idx := refinementIndexCode alpha (s.encode V) (s.encode E) U.val.val Rf.val.val Rc.val.val
  let gamma := insert alpha alpha
  let hGamma := M.insert_mem pairing unions hAlpha hAlpha
  let gammaOrdinal := ordinalSetProperty_succ cutOrdinal
  let alphaGamma : alpha ⊆ gamma := fun x hx => ZFSet.mem_insert_of_mem alpha hx
  let gammaSubset : gamma ⊆ stages := fun x hx =>
    Or.elim (Iff.mp ZFSet.mem_insert_iff hx)
      (fun equal => Eq.mpr (congrArg (fun z => z ∈ stages) equal) member)
      (fun old => subset x old)
  let gammaPacked := graphRestriction gamma packed
  let gammaPackedGround := M.graphRestriction_mem unions separation hGamma hPacked
  let gammaRun := historyRun.restrict gammaOrdinal gammaSubset
  let middleSet := M.refinementHistoryForcing c.carrier lifted gamma gammaPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted gamma gammaPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted gamma gammaPacked
    gammaRun.carriers gammaOrdinal carrier (c.encode ⊤) topMem topRows
  let middle := SetMembers.presentation middleSet
  let gammaMono := fun level fields (entry : ZFSet.pair level (refinementFormulaDataCode fields) ∈ gammaPacked) => mono level fields
    (And.left (Iff.mp pair_mem_graphRestriction entry))
  let nestedInclude := RecursiveRefinementOrderHistory.inclusionFunction gammaRun gammaOrdinal cutOrdinal alphaGamma
    pairing unions powers separation infinite choice hGamma gammaPackedGround hLifted hAlpha carrier
    (c.encode ⊤) topMem topRows gammaMono
  let toNested := fun x : SetMembers Q => SetMembers.ofMem (SetMembers.raw x)
    (Eq.mpr (congrArg (fun h => SetMembers.raw x ∈ M.refinementHistoryForcing c.carrier lifted alpha h)
      (graphRestriction_restrict alphaGamma)) (SetMembers.raw_mem x))
  let prefixInclude := fun x : SetMembers Q => nestedInclude (toNested x)
  let successorLabel := Name.refinementAssignmentLabel middle prefixInclude ⊤ lifted localValid idx Rf.val Rc.val
  let middleAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hh trace hGamma gammaOrdinal gammaSubset
  let lift := M.semanticStructuralNameLift c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace hGamma gammaOrdinal gammaSubset infinite choice
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  have canonical := M.semanticStructuralAssignmentLabel_canonical_successor_name c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace member infinite choice V E U Rf Rc index
  obtain ⟨Uc, Rfc, Rcc, uEq, fineEq, coarseEq, canonicalIndex, labelEq, canonicalGround,
    canonicalSupport, canonicalHS, ground, supported, hsName, liftedEq, liftedGround,
    liftedSupport, liftedHS, same⟩ := canonical
  refine ⟨ground, supported, hsName, liftedEq.trans labelEq, liftedGround, liftedSupport, liftedHS, ?_⟩
  intro H ordinary
  have injection := fulfilled.structural_assignment_label_injection collection infinite choice labels
    small smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace alpha member V E U Rf Rc index H ordinary
  dsimp only at injection
  rw [same H] at injection
  exact ⟨same H, injection⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
