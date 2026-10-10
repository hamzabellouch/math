import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalFairPreparationOrbits

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v

def FairPreparationLowerBoundResult (M : TransitiveGround.{u})
    {R : Type u} [PartialOrder R] (c : Presentation R)
    (T stages packed nodes p : ZFSet.{u}) : Prop :=
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let upperOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let relation := M.varyingPreparationRelation stages packed upperQ upperOrder nodes T
  let B := M.groundSmallSubsets
    (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
  let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
  let data := flatCarrierData c upperQ B shape
    ∃ enumSelector ∈ M.sets,
        ZFSet.IsFunc upperQ (M.groundRelations ZFSet.omega stages) enumSelector ∧
        enumSelector ⊆ M.birthLevelEnumerationRelation upperQ stages
          (refinementDataHistoryLevels stages packed T) ∧
      ∃ E0 ∈ M.sets, ZFSet.IsFunc upperQ E0 enumSelector ∧
      ∃ prepSelector ∈ M.sets,
        ZFSet.IsFunc (ZFSet.prod stages upperQ)
          (M.preparationWitnessBound nodes T upperQ) prepSelector ∧
        prepSelector ⊆ relation ∧
      ∃ seq : Nat → SetMembers upperQ, SetMembers.raw (seq 0) = p ∧
        groundSequenceGraph seq ∈ M.sets ∧
        (∀ i j : Nat, i ≤ j → ZFSet.pair (SetMembers.raw (seq j)) (SetMembers.raw (seq i)) ∈ upperOrder) ∧
      ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧
      ∃ clocks births events : Nat → ZFSet.{u},
        clocks 0 = ∅ ∧ births 0 = {ZFSet.pair ∅ e} ∧ events 0 = ∅ ∧
        (∀ k, FairPreparationStepCode ZFSet.omega E0 stages
          (M.preparationWitnessBound nodes T upperQ) enumSelector prepSelector
          (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
          (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k)) (ZFSet.pair (births k) (events k))))
          (ZFSet.pair (clocks (k + 1))
            (ZFSet.pair (SetMembers.raw (seq (k + 1))) (ZFSet.pair (births (k + 1)) (events (k + 1)))))) ∧
      ∃ limit : SetMembers upperQ,
        (∀ n, ZFSet.pair (SetMembers.raw limit) (SetMembers.raw (seq n)) ∈ upperOrder) ∧
        SetMembers.raw (data limit) = stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∧
        stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∈ M.sets ∧
        (∀ z, z ∈ SetMembers.raw (data limit) ↔ ∃ n, z ∈ SetMembers.raw (data (seq n))) ∧
        ∀ x ∈ SetMembers.raw (data limit),
          ∃ i j : Nat, ∃ alpha ∈ stages, ∃ fields : Fin 15 → ZFSet.{u},
            Nat.unpair (Nat.pair i j) = (i, j) ∧ i ≤ Nat.pair i j ∧
            x ∈ SetMembers.raw (data (seq i)) ∧
            ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
            ZFSet.pair x alpha ∈ refinementDataHistoryLevels stages packed T ∧
            (∀ k, Nat.pair i j ≤ k →
              x ∈ assignmentOnIndices (fields 0) T (SetMembers.raw (data (seq k)))) ∧
            ∃ y ∈ M.preparationWitnessBound nodes T upperQ, ∃ payload,
              y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
              ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
              events (Nat.pair i j + 1) = ZFSet.pair alpha y

variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {R : Type u} [PartialOrder R] (c : Presentation R)

theorem exists_groundFairPreparationLowerBound
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
    ∀ p ∈ upperQ, FairPreparationLowerBoundResult M c T stages packed b.carrier p := by
  let geometry := run.finalGeometry i₀
  let instGeometryGroup := geometry.group_code.toGroup
  let instGeometryOrder := geometry.meet.order.toPartialOrder
  let instGeometryBottom := geometry.decodedBottom
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
  let instHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let pTyped : SetMembers upperQ := SetMembers.ofMem p hp
  have typedChosen : ZFSet.pair (SetMembers.raw pTyped) e ∈ enumSelector := by
    simpa only [pTyped, SetMembers.raw_ofMem] using chosen
  have typedInitial : ∀ state, ZFSet.pair ∅ state ∈ orbit ↔
      state = ZFSet.pair ∅ (ZFSet.pair (SetMembers.raw pTyped) (ZFSet.pair {ZFSet.pair ∅ e} ∅)) := by
    simpa only [pTyped, SetMembers.raw_ofMem] using initial
  obtain ⟨seq, start, seqGround, decreasing, clocks, births, events,
      clockZero, birthZero, eventZero, rawSteps, limit, below, dataEqual,
      unionGround, exactEntries, visits⟩ :=
    M.semanticStructuralFairPreparation_lower_bound c a t b d ⊥ directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrder rowAction
      geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
      hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hs hh ordinal trace infinite choice rowClosed pTyped E0 enumSelector prepSelector orbit e
      hE0 hOrbit rangeFunction enumSelected prepSelected typedChosen orbitFunction typedInitial steps
  refine ⟨enumSelector, hEnum, enumFunction, enumSelected, E0, hE0, rangeFunction,
    prepSelector, hPrep, prepFunction, prepSelected, seq, ?_, seqGround, (fun _ _ h => decreasing h),
    e, he, chosen, clocks, births, events, clockZero, birthZero, eventZero, rawSteps,
    limit, below, dataEqual, unionGround, exactEntries, visits⟩
  exact (congrArg SetMembers.raw start).trans (SetMembers.raw_ofMem p hp)

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {R : Type u} [PartialOrder R]

theorem FairPreparationLowerBoundResult.exists_storedPreparedLimit
    (c : Presentation R)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {T stages packed nodes p : ZFSet.{u}}
    (run : RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages packed)
    (environments : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
        StoredPreparationEnvironment M fields)
    (result : FairPreparationLowerBoundResult M c T stages packed nodes p) :
    ∃ limit ∈ M.refinementHistoryForcing c.carrier T stages packed,
      ZFSet.pair limit p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
      StoredPreparedConditionCode M c.carrier T stages packed nodes limit := by
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  let order := M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed
  let B := M.groundSmallSubsets
    (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
  let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
  let data := flatCarrierData c Q B shape
  let row := flatCarrierRow c Q B shape
  obtain ⟨enumSelector, _hEnum, _enumFunction, _enumSelected, E0, _hE0, _rangeFunction,
    prepSelector, _hPrep, _prepFunction, prepSelected, seq, start, _seqGround, _decreasing,
    e, _he, _chosen, clocks, births, events, _clockZero, _birthZero, _eventZero, _rawSteps,
    limit, below, _dataEqual, _unionGround, _exactEntries, visits⟩ := result
  refine ⟨SetMembers.raw limit, SetMembers.raw_mem limit, ?_, ?_⟩
  · exact start ▸ below 0
  intro limitRow limitA limitCode x hx
  have limitData : SetMembers.raw (data limit) = limitA :=
    (ZFSet.pair_inj.1 ((flatCarrier_coordinates c Q B shape limit).symm.trans limitCode)).2
  have inData : x ∈ SetMembers.raw (data limit) := limitData.symm ▸ hx
  obtain ⟨i, j, alpha, hAlpha, fields, _unpaired, _born, _early, stored, _level,
    retained, y, _hy, payload, yCode, selected, _event⟩ := visits x inData
  let n := Nat.pair i j
  have relationEntry := prepSelected selected
  rw [yCode] at relationEntry
  obtain ⟨_, _inputMember, bounded, other, otherStored, terms, nodeCarrier, meetCode, code⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed Q order nodes T alpha
      (SetMembers.raw (seq n)) (ZFSet.pair (SetMembers.raw (seq (n + 1))) payload)).1 relationEntry
  have same : other = fields :=
    refinementFormulaDataCode_injective (run.carriers.data.function.unique otherStored stored)
  subst other
  obtain ⟨sourceRow, sourceA, output, k, enumerations, q,
    inputCode, outputCode, _visitBelow, cut, family⟩ := code
  have sourceData : SetMembers.raw (data (seq n)) = sourceA :=
    (ZFSet.pair_inj.1 ((flatCarrier_coordinates c Q B shape (seq n)).symm.trans inputCode)).2
  obtain ⟨outputEq, payloadEq⟩ := ZFSet.pair_inj.1 outputCode
  subst output
  rw [payloadEq] at bounded
  obtain ⟨_, hkBound, heBound⟩ := (M.mem_preparationWitnessBound nodes T Q
    (SetMembers.raw (seq (n + 1))) k enumerations).1 bounded
  have hk := ((M.mem_groundRelations _ _ k).1 hkBound).1
  have hEnumerations := ((M.mem_groundRelations _ _ enumerations).1 heBound).1
  have hSourceA : sourceA ∈ M.sets := sourceData ▸
    ((M.mem_groundSmallSubsets _ _ _).1 (SetMembers.raw_mem (data (seq n)))).1
  have sourceMember : ZFSet.pair sourceRow sourceA ∈ Q := inputCode ▸ SetMembers.raw_mem (seq n)
  have sourceBelow := below n
  rw [limitCode, inputCode] at sourceBelow
  have sourceSubset := ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
    stages packed limitRow limitA sourceRow sourceA).1 sourceBelow).2.2.2
  have sourceSelected : x ∈ assignmentOnIndices (fields 0) T sourceA :=
    sourceData ▸ retained n (Nat.le_refl n)
  have environment := environments alpha fields stored
  obtain ⟨rCut, hrCut, finalCut, _cutBelow, finalFamily⟩ :=
    M.storedPreparationFamily_cut_mono pairing unions powers separation collection run fields
      environment stored hSourceA (SetMembers.raw_mem limit) (below (n + 1)) cut family
  exact ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meetCode, environment,
    sourceRow, sourceA, hSourceA, sourceMember, sourceSubset, sourceSelected,
    k, hk, enumerations, hEnumerations, rCut, hrCut, finalCut, finalFamily⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
