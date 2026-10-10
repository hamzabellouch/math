import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAugmentedClassRequests
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundAssignmentRequestBatches

namespace OAI

open scoped ZFSet



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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
include hs hh ordinal trace

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace

theorem semanticStructuralTrace_assignmentRequestBatch
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    let levels := relationImage A stages (refinementDataHistoryLevels stages packed T)
    levels ∈ M.sets ∧ M.groundEmbeddable levels ZFSet.omega ∧ levels ⊆ stages ∧
    ∃ families : Fin 2 → ZFSet.{u},
      (∀ side, families side ∈ M.sets ∧ FunctionGraphOn levels (families side)) ∧
      (∀ side alpha (fields : Fin 15 → ZFSet.{u}),
        ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
        ∀ graph, ZFSet.pair alpha graph ∈ families side ↔
          alpha ∈ levels ∧ graph = M.storedAssignmentClassGraph A fields side) ∧
      let flat := fun side => ⋃₀ functionGraphRange levels (families side)
      let requests := fun side => functionGraphRange A (flat side)
      (∀ side, flat side ∈ M.sets ∧ FunctionGraphOn A (flat side)) ∧
      (requests 0 ∪ requests 1) ∈ M.sets ∧
      M.groundEmbeddable (requests 0 ∪ requests 1) ZFSet.omega ∧
      ∀ alpha (member : alpha ∈ stages),
        let lowerPacked := graphRestriction alpha packed
        let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
        letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
        letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
          ((run).carriers.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member))
          (ordinalSetProperty_member ordinal member) carrier rowTop topMem topRows
        let lower := SetMembers.presentation Q
        let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
          pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
          nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
          topMem topRows hh trace (M.transitive hs member)
          (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member)
        let valid := M.refinementHistoryRowNameFamily_valid c
          ((run).carriers.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member))
          (ordinalSetProperty_member ordinal member) carrier T valid1
        let I := M.niceRefinementIndices act lower b d alpha T T2 valid
        let selected := assignmentOnIndices I T A
        let graphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid selected
        let bound := M.groundRelations T lower.carrier
        let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
        (∀ side graph, ZFSet.pair alpha graph ∈ families side ↔
          alpha ∈ levels ∧ graph = graphs side) ∧
        selected ∈ M.sets ∧ M.groundEmbeddable selected ZFSet.omega ∧
        (∀ side, graphs side ∈ M.sets ∧ ZFSet.IsFunc selected bound (graphs side)) ∧
        J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
        (∀ z ∈ J, IsName lower z) ∧
        ∀ z : Name lower, z.val ∈ J →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) z ∧
          ∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} z ⊆
            Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := by
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have candidate := ((M.mem_refinementHistoryForcing c.carrier T stages packed _).1 condition).1
  obtain ⟨_, hA, shape, smallA⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  have localFunctions : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
      ∀ side, FunctionGraphOn (assignmentOnIndices (fields 0) T A)
        (M.storedAssignmentClassGraph A fields side) := by
    intro alpha fields stored side
    have member := (run).carriers.data.function.pair_source stored
    let lowerPacked := graphRestriction alpha packed
    let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
    let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member))
      (ordinalSetProperty_member ordinal member) carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hh trace (M.transitive hs member)
      (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member)
    let valid := M.refinementHistoryRowNameFamily_valid c
      ((run).carriers.restrict (ordinalSetProperty_member ordinal member) (ordinal.1 alpha member))
      (ordinalSetProperty_member ordinal member) carrier T valid1
    have exactStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
    have same : fields = M.refinementLevelFormulaData act lower b d alpha T T2 valid :=
      refinementFormulaDataCode_injective ((run).carriers.data.function.unique stored exactStored)
    subst fields
    have facts := M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice condition
    exact ⟨M.groundRelations T lower.carrier, (facts.2.2.1 side).2⟩
  obtain ⟨hLevels, smallLevels, inside, families, grounds, entries, flatFacts, groundRequests, smallRequests⟩ :=
    M.exists_assignmentRequestBatch pairing unions powers separation collection infinite choice hs hPacked hT
      hA smallA (run).carriers.data shape localFunctions
  refine ⟨hLevels, smallLevels, inside, families, grounds, entries, flatFacts, groundRequests, smallRequests, ?_⟩
  intro alpha member
  dsimp only
  have exactStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have facts := M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice condition
  refine ⟨fun side graph => entries side alpha _ exactStored graph, facts.1, facts.2.1, facts.2.2.1,
    facts.2.2.2.1, facts.2.2.2.2.1, facts.2.2.2.2.2.1, facts.2.2.2.2.2.2.1⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
