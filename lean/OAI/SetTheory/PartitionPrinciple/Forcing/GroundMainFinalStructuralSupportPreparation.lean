import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticFairPreparationSupportedLimits
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundFixedFairPreparationLimitCertificates
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainFinalStructuralPrefixDescent

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v

def GroundSupportPreparedStrengtheningResult (M : TransitiveGround.{u})
    {R : Type u} [PartialOrder R] (c : Presentation R)
    (T stages packed nodes p : ZFSet.{u}) : Prop :=
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  ∃ q ∈ Q,
    ZFSet.pair q p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
    ∃ S ∈ M.sets, S ⊆ nodes ∧ M.groundEmbeddable S ZFSet.omega ∧
      StoredSupportPreparedConditionCode M c.carrier T stages packed nodes q S

variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {R : Type u} [PartialOrder R] (c : Presentation R)

theorem exists_groundSupportPreparedStrengthening
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    ∀ (_descent : ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
    ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val
    ),
    ∀ p ∈ upperQ, GroundSupportPreparedStrengtheningResult M c T stages packed b.carrier p := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
  intro stages history hs hh ordinal trace
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T
  intro descent p hp
  refine Exists.elim
    (fulfilled.exists_groundFairPreparationOrbit c collection infinite choice small smallD irreflexive rowClosed
      a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2 children1 children2
      topMem topRows stages history hs hh ordinal trace descent p hp)
    (fun enumSelector enumRest => ?_)
  have hEnum := enumRest.1
  have enumFunction := enumRest.2.1
  have enumSelected := enumRest.2.2.1
  refine Exists.elim enumRest.2.2.2 (fun E0 rangeRest => ?_)
  have hE0 := rangeRest.1
  have rangeFunction := rangeRest.2.1
  refine Exists.elim rangeRest.2.2 (fun prepSelector prepRest => ?_)
  have hPrep := prepRest.1
  have prepFunction := prepRest.2.1
  have prepSelected := prepRest.2.2.1
  refine Exists.elim prepRest.2.2.2 (fun e eRest => ?_)
  have he := eRest.1
  have chosen := eRest.2.1
  refine Exists.elim eRest.2.2 (fun orbit orbitRest => ?_)
  have hOrbit := orbitRest.1
  have orbitFunction := orbitRest.2.1
  have initial := orbitRest.2.2.1
  have steps := orbitRest.2.2.2
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let pTyped : SetMembers upperQ := SetMembers.ofMem p hp
  have typedChosen : ZFSet.pair (SetMembers.raw pTyped) e ∈ enumSelector := by
    simpa only [pTyped, SetMembers.raw_ofMem] using chosen
  have typedInitial : ∀ state, ZFSet.pair ∅ state ∈ orbit ↔
      state = ZFSet.pair ∅ (ZFSet.pair (SetMembers.raw pTyped) (ZFSet.pair {ZFSet.pair ∅ e} ∅)) := by
    simpa only [pTyped, SetMembers.raw_ofMem] using initial
  obtain ⟨seq, start, seqGround, decreasing, clocks, births, events,
      clockZero, birthZero, eventZero, entries, eventGround, eventFunction,
      supportGround, supportSubset, supportSmall, rawSteps, limit, below, dataEqual,
      unionGround, exactEntries, visits⟩ :=
    M.semanticStructuralFairPreparation_supported_lower_bound c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction
      geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
      hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hs hh ordinal trace infinite choice rowClosed pTyped E0 enumSelector prepSelector orbit e
      hE0 hOrbit rangeFunction enumSelected prepSelected typedChosen orbitFunction typedInitial steps
  have initialRaw : SetMembers.raw (seq 0) = p :=
    (congrArg SetMembers.raw start).trans (SetMembers.raw_ofMem p hp)
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let U := M.preparationWitnessBound b.carrier T upperQ
  let E := insert ∅ (ZFSet.prod stages U)
  let supportSet := M.preparationUsedSupportUnion b.carrier E (familyCodeGraph natSetCode events)
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrder
      (Fin.cases supports (Fin.cases hT (Fin.cases hT2 (Fin.cases hs
        (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hUpper := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hU := M.preparationWitnessBound_mem pairing unions powers separation
    geometry.carrier_ground hT hUpper omega
  have hE := M.insert_mem pairing unions (M.empty_mem ⟨upperQ, hUpper⟩)
    (M.prod_mem pairing unions powers separation hs hU)
  have environments : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
        StoredPreparationEnvironment M fields := by
    intro alpha fields stored
    have member := historyRun.carriers.data.function.pair_source stored
    exact M.semanticStructuralPrefix_preparationEnvironment c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction
      geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
      hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hs hh ordinal trace member fields stored
  refine ⟨SetMembers.raw limit, SetMembers.raw_mem limit, initialRaw ▸ below 0,
    supportSet, supportGround, supportSubset, supportSmall, ?_⟩
  exact M.fixedFairPreparationLimit_supportPrepared c pairing unions powers separation collection
    historyRun environments geometry.carrier_ground hE prepSelected seq events eventFunction
    limit below visits

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
open scoped ZFSet
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_support_prepared_strengthening
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
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  ∀ p ∈ upperQ,
    GroundSupportPreparedStrengtheningResult M c lifted stages packed s.carrier p := by
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
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
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
  intro p member
  have descent := fulfilled.structural_prefix_descent
    collection infinite choice small smallD irreflexive columns hColumns hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation
    infinite choice coordinates two
  exact fulfilled.exists_groundSupportPreparedStrengthening c
    collection infinite choice small smallD irreflexive rowClosed act lifted squared (c.encode ⊤)
    carrier forcingOrder forcingAction hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    topMem topRows stages history hs hh stagesOrdinal trace descent p member

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
