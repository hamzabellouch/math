import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticFairPreparationLimits

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def fairPreparationEventGraph
    (Q stages U E0 orbit : ZFSet.{u}) : ZFSet.{u} :=
  let histories := M.groundRelations ZFSet.omega E0
  let events := insert ∅ (ZFSet.prod stages U)
  let tail := ZFSet.prod histories events
  let middle := ZFSet.prod Q tail
  let bound := ZFSet.prod ZFSet.omega middle
  relationCompose ZFSet.omega tail events
    (relationCompose ZFSet.omega middle tail
      (relationCompose ZFSet.omega bound middle orbit (productSecond ZFSet.omega middle))
      (productSecond Q tail))
    (productSecond histories events)

theorem fairPreparationEventGraph_function
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit) :
    ZFSet.IsFunc ZFSet.omega (insert ∅ (ZFSet.prod stages U))
      (M.fairPreparationEventGraph Q stages U E0 orbit) := by
  let histories := M.groundRelations ZFSet.omega E0
  let events := insert ∅ (ZFSet.prod stages U)
  let tail := ZFSet.prod histories events
  let middle := ZFSet.prod Q tail
  have widened : ZFSet.IsFunc ZFSet.omega (ZFSet.prod ZFSet.omega middle) orbit := by
    refine ⟨?_, function.2⟩
    intro z member
    obtain ⟨i, hi, state, hs, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨hi, ((M.mem_fairPreparationStates _ _ _ _ _ _).1 hs).1⟩
  exact relationCompose_function_of_subset
    (relationCompose_function_of_subset
      (relationCompose_function_of_subset widened
        (productSecond_function ZFSet.omega middle) (fun _ h => h))
      (productSecond_function Q tail) (fun _ h => h))
    (productSecond_function histories events) (fun _ h => h)

theorem pair_mem_fairPreparationEventGraph
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (i event : ZFSet.{u}) :
    ZFSet.pair i event ∈ M.fairPreparationEventGraph Q stages U E0 orbit ↔
      ∃ clock p births,
        ZFSet.pair i (ZFSet.pair clock (ZFSet.pair p (ZFSet.pair births event))) ∈ orbit := by
  dsimp only [fairPreparationEventGraph]
  rw [pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, tail, _, second, projectedEvent⟩
    obtain ⟨births, hb, event', he, equal⟩ := (mem_productSecond _ _ _).1 projectedEvent
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨_, _, middle, _, first, projectedTail⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
    obtain ⟨p, hp, tail', ht, equal⟩ := (mem_productSecond _ _ _).1 projectedTail
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨_, _, state, _, edge, projectedMiddle⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨clock, hc, middle', hm, equal⟩ := (mem_productSecond _ _ _).1 projectedMiddle
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨clock, p, births, edge⟩
  · rintro ⟨clock, p, births, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have stateBound := ((M.mem_fairPreparationStates _ _ _ _ _ _).1 bounds.2).1
    have split := ZFSet.pair_mem_prod.1 stateBound
    have middle := ZFSet.pair_mem_prod.1 split.2
    have tail := ZFSet.pair_mem_prod.1 middle.2
    refine ⟨bounds.1, tail.2, _, middle.2, ?_, ?_⟩
    · refine (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨bounds.1, middle.2, _, split.2, ?_, ?_⟩
      · exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
          ⟨bounds.1, split.2, _, stateBound, edge,
            (mem_productSecond _ _ _).2 ⟨clock, split.1, _, split.2, rfl⟩⟩
      · exact (mem_productSecond _ _ _).2 ⟨p, middle.1, _, middle.2, rfl⟩
    · exact (mem_productSecond _ _ _).2 ⟨births, tail.1, event, tail.2, rfl⟩

theorem fairPreparationEventGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages U E0 orbit : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (whole : orbit ∈ M.sets) :
    M.fairPreparationEventGraph Q stages U E0 orbit ∈ M.sets := by
  have hHistories := M.groundRelations_mem pairing unions powers separation omega hE0
  have hEvents := M.insert_mem pairing unions (M.empty_mem ⟨Q, hQ⟩)
    (M.prod_mem pairing unions powers separation hStages hU)
  have hTail := M.prod_mem pairing unions powers separation hHistories hEvents
  have hMiddle := M.prod_mem pairing unions powers separation hQ hTail
  exact M.relationCompose_mem pairing unions powers separation omega hTail hEvents
    (M.relationCompose_mem pairing unions powers separation omega hMiddle hTail
      (M.relationCompose_mem pairing unions powers separation omega
        (M.prod_mem pairing unions powers separation omega hMiddle) hMiddle whole
        (M.productSecond_mem pairing unions powers separation omega hMiddle))
      (M.productSecond_mem pairing unions powers separation hQ hTail))
    (M.productSecond_mem pairing unions powers separation hHistories hEvents)

theorem fairPreparationEvents_graph_eq
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (clocks conditions births events : Nat → ZFSet.{u})
    (entries : ∀ k, ZFSet.pair (natSetCode k)
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k)))) ∈ orbit) :
    familyCodeGraph natSetCode events = M.fairPreparationEventGraph Q stages U E0 orbit := by
  have domain : ZFSet.range (natSetCode : Nat → ZFSet.{u}) = ZFSet.omega := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_range, mem_omega_iff_natSetCode]
    exact ⟨fun ⟨n, h⟩ => ⟨n, h.symm⟩, fun ⟨n, h⟩ => ⟨n, h.symm⟩⟩
  exact familyCodeGraph_eq_of_entries ⟨_, M.fairPreparationEventGraph_function function⟩
    natSetCode events domain (fun k =>
      (M.pair_mem_fairPreparationEventGraph function _ _).2 ⟨clocks k, conditions k, births k, entries k⟩)

theorem fairPreparationEvents_ground_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q stages U E0 enumSelector orbit : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hStages : stages ∈ M.sets) (hU : U ∈ M.sets)
    (hE0 : E0 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) (whole : orbit ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (clocks conditions births events : Nat → ZFSet.{u})
    (entries : ∀ k, ZFSet.pair (natSetCode k)
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k)))) ∈ orbit) :
    familyCodeGraph natSetCode events ∈ M.sets ∧
      ZFSet.IsFunc ZFSet.omega (insert ∅ (ZFSet.prod stages U)) (familyCodeGraph natSetCode events) := by
  rw [M.fairPreparationEvents_graph_eq function clocks conditions births events entries]
  exact ⟨M.fairPreparationEventGraph_mem pairing unions powers separation hQ hStages hU hE0 omega whole,
    M.fairPreparationEventGraph_function function⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

theorem semanticStructuralFairPreparation_recorded_lower_bound
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let B := M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
    let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
    let data := flatCarrierData c Q B shape
    ∀ (p : SetMembers Q) (E0 enumSelector prepSelector orbit e : ZFSet.{u}),
      E0 ∈ M.sets → orbit ∈ M.sets →
      ZFSet.IsFunc Q E0 enumSelector →
      enumSelector ⊆ M.birthLevelEnumerationRelation Q stages (refinementDataHistoryLevels stages packed T) →
      prepSelector ⊆ M.varyingPreparationRelation stages packed Q
        (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) b.carrier T →
      ZFSet.pair (SetMembers.raw p) e ∈ enumSelector →
      ZFSet.IsFunc ZFSet.omega
        (M.fairPreparationStates Q stages (M.preparationWitnessBound b.carrier T Q) E0 enumSelector) orbit →
      (∀ state, ZFSet.pair ∅ state ∈ orbit ↔
        state = ZFSet.pair ∅ (ZFSet.pair (SetMembers.raw p) (ZFSet.pair {ZFSet.pair ∅ e} ∅))) →
      (∀ n ∈ ZFSet.omega, ∀ state next,
        ZFSet.pair n state ∈ orbit → ZFSet.pair (insert n n) next ∈ orbit →
        FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T Q)
          enumSelector prepSelector
          (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv) state next) →
      ∃ seq : Nat → SetMembers Q, seq 0 = p ∧ groundSequenceGraph seq ∈ M.sets ∧ Antitone seq ∧
      ∃ clocks births events : Nat → ZFSet.{u},
        clocks 0 = ∅ ∧ births 0 = {ZFSet.pair ∅ e} ∧ events 0 = ∅ ∧
        (∀ k, ZFSet.pair (natSetCode k)
          (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k))
            (ZFSet.pair (births k) (events k)))) ∈ orbit) ∧
        familyCodeGraph natSetCode events ∈ M.sets ∧
        ZFSet.IsFunc ZFSet.omega
          (insert ∅ (ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)))
          (familyCodeGraph natSetCode events) ∧
        (∀ k, FairPreparationStepCode ZFSet.omega E0 stages (M.preparationWitnessBound b.carrier T Q)
          enumSelector prepSelector
          (natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv)
          (ZFSet.pair (clocks k) (ZFSet.pair (SetMembers.raw (seq k)) (ZFSet.pair (births k) (events k))))
          (ZFSet.pair (clocks (k + 1))
            (ZFSet.pair (SetMembers.raw (seq (k + 1))) (ZFSet.pair (births (k + 1)) (events (k + 1)))))) ∧
      ∃ limit : SetMembers Q, (∀ n, limit ≤ seq n) ∧
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
            ∃ y ∈ M.preparationWitnessBound b.carrier T Q, ∃ payload,
              y = ZFSet.pair (SetMembers.raw (seq (Nat.pair i j + 1))) payload ∧
              ZFSet.pair (ZFSet.pair alpha (SetMembers.raw (seq (Nat.pair i j)))) y ∈ prepSelector ∧
              events (Nat.pair i j + 1) = ZFSet.pair alpha y := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  let upper := SetMembers.presentation Q
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hU := M.preparationWitnessBound_mem pairing unions powers separation nodes hT hQ omega
  dsimp only
  intro p E0 enumSelector prepSelector orbit e hE0 whole enumFunction enumSelected
    prepSelected chosen orbitFunction initial steps
  have selected : prepSelector ⊆ M.varyingPreparationRelation stages packed
      upper.carrier upper.conditionOrder b.carrier T := by
    exact Eq.mpr (congrArg
      (fun order => prepSelector ⊆ M.varyingPreparationRelation stages packed Q order b.carrier T)
      (M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed)) prepSelected
  obtain ⟨seq, start, seqGround, decreasing, clocks, births, events,
      clockZero, birthZero, eventZero, entries, rawSteps⟩ :=
    M.fairPreparationOrbit_conditionSequence upper pairing unions powers separation
      hQ hs hU hE0 omega whole orbitFunction selected p e initial steps
  have eventGraph := M.fairPreparationEvents_ground_function pairing unions powers separation
    hQ hs hU hE0 omega whole orbitFunction clocks
    (fun k => SetMembers.raw (seq k)) births events entries
  obtain ⟨_q, _belowRows, limit, _code, below, dataEqual, unionGround, exactEntries⟩ :=
    M.semanticStructuralTrace_exact_assignment_union c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
      nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
      symmetric1 symmetric2 topMem topRows hs hh ordinal trace infinite choice rowClosed seq seqGround decreasing
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have initialChosen : ZFSet.pair (SetMembers.raw (seq 0)) e ∈ enumSelector := start.symm ▸ chosen
  refine ⟨seq, start, seqGround, decreasing, clocks, births, events, clockZero, birthZero, eventZero,
    entries, eventGraph.1, eventGraph.2, rawSteps, limit, below, dataEqual, unionGround, exactEntries, ?_⟩
  intro x member
  exact M.fairRefinementSequence_assignment_prepared c T stages packed run.carriers.data
    enumFunction enumSelected seq decreasing clocks births events e initialChosen clockZero birthZero
    rawSteps x (dataEqual ▸ member)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
