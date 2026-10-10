import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFairPreparationConditionSequences
import OAI.SetTheory.PartitionPrinciple.Forcing.StructuralForcingStageWitnessStep
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFairRefinementAssignmentVisits
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundStructuralCompleteProjections
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRefinementInternalClosure

namespace OAI



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

theorem structuralForcingTrace_witnesses
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history) :
    ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      RawRefinementStageWitness M t b d base directed T T2 level P order top action := by
  apply M.structuralTrace_stageWitnesses t b d c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    T T2 base directed unions separation ?_ hs hh ordinal trace
  intro level prior hl hp ord run earlier P order top action output
  exact structuralForcingStage_witness_step M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hl hp ord run earlier P order top action output

theorem exists_semanticStructuralForcingHistory
    {stages : ZFSet.{u}} (hs : stages ∈ M.sets) (ordinal : ordinalSetProperty stages) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history ∧
      M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history ∈ M.sets ∧
      RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 stages history) ∧
      ∀ level P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history →
        RawRefinementStageWitness M t b d base directed T T2 level P order top action := by
  let params : Fin 12 → ZFSet.{u} := ![c.carrier, c.conditionOrder, rowTop, a.actionGraph c t,
    t.carrier, b.carrier, b.conditionOrder, d.actionGraph b t,
    supportBasisCode b t d.principalFix, T, T2, ZFSet.omega]
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases carrier (Fin.cases rowOrderGround (Fin.cases (M.transitive carrier topMem)
      (Fin.cases rowAction (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder
        (Fin.cases nodeAction (Fin.cases supports (Fin.cases hT (Fin.cases hT2
          (Fin.cases omega (fun j => Fin.elim0 j))))))))))))
  obtain ⟨history, hh, trace, hPacked, run, _orderTop⟩ :=
    M.exists_structuralForcingHistory pairing unions powers separation collection params members rfl hs ordinal
      c.conditionOrder_code topMem topRows
  exact ⟨history, hh, trace, hPacked, run,
    structuralForcingTrace_witnesses M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [OrderTop R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem pairEmpty_semanticStructuralHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
    (action : a.actionGraph c t ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName c z)
    (closed : ∀ g (tau : Name c), tau.val ∈ T → (a.act c g tau).val ∈ T)
    (children : ∀ tau : Name c, tau.val ∈ T →
      HereditarilySymmetric a c (d.principalSupportFamily base directed) tau) :
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let graph := Name.renameFamilyGraph c.pairEmpty id T valid
    lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
      (∀ z ∈ lifted, IsName c.pairEmpty z) ∧ (∀ z ∈ squared, IsName c.pairEmpty z) ∧
      (∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (a.act c.pairEmpty g tau).val ∈ lifted) ∧
      (∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (a.act c.pairEmpty g tau).val ∈ squared) ∧
      (∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau) ∧
      (∀ tau : Name c.pairEmpty, tau.val ∈ squared →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau) ∧
      ∀ stages ∈ M.sets, ordinalSetProperty stages → ∃ history ∈ M.sets,
        OrdinalRecursionTrace (fun level prior stage => stage =
          M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (a.actionGraph c t)
            t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
            (supportBasisCode b t d.principalFix) lifted squared level prior) stages history ∧
        M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) lifted squared stages history ∈ M.sets ∧
        RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted stages
          (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
            (supportBasisCode b t d.principalFix) lifted squared stages history) ∧
        ∀ level P order top action,
          ZFSet.pair level (forcingStageCode P order top action) ∈ history →
          RawRefinementStageWitness M t b d base directed lifted squared level P order top action := by
  obtain ⟨hLifted, hGraph, injection, valid1, hs1, closed1, _⟩ :=
    M.pairEmpty_nameFamily a c (d.principalSupportFamily base directed)
      pairing unions powers separation collection carrier T hT valid closed children
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  have pairedCarrier := M.pairEmpty_carrier_mem pairing unions powers separation c carrier
  have hTop := M.transitive pairedCarrier (c.pairEmpty.encode_mem ⊤)
  have hSquared : squared ∈ M.sets :=
    M.orderedPairNameFamily_mem pairing unions powers separation hTop hLifted hLifted
  have valid2 : ∀ z ∈ squared, IsName c.pairEmpty z := orderedPairNameFamily_valid ⊤ valid1 valid1
  have closed2 := orderedPairNameFamily_closed a valid1 valid1 closed1 closed1
  have hs2 := orderedPairNameFamily_hs a (d.principalSupportFamily base directed) valid1 valid1 hs1 hs1
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation collection
    nodes group nodeAction
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  refine ⟨hLifted, hSquared, hGraph, injection, valid1, valid2, closed1, closed2, hs1, hs2, ?_⟩
  intro stages hStages ordinal
  exact M.exists_semanticStructuralForcingHistory c a t b d base directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier order action group nodes nodeOrder nodeAction
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 hs1 hs2
    (c.encode_mem ⊤) topRows hStages ordinal

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

theorem semanticStructuralTrace_binary_union_extension
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    ∀ row A B : ZFSet.{u},
      ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      ZFSet.pair row B ∈ M.refinementHistoryForcing c.carrier T stages packed →
      AssignmentIndexAgreement A B →
      ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair row A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair row B) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  dsimp only
  intro row A B first second agreement
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact run.binary_union_extension pairing unions powers separation infinite choice hs hPacked hT
    ordinal mono c.conditionOrder_code first second agreement

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

theorem semanticStructuralTrace_completeProjection
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (alpha : ZFSet.{u}) (hAlpha : alpha ∈ M.sets)
    (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
      T T2 ordinal trace
    let witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace
    let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
      pairing unions powers separation collection group nodes supports hh hT witnesses
    let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    CompleteProjection (run.restriction ordinal cutOrdinal subset c.conditionOrder_code)
      (run.inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
        hs hPacked hT hAlpha carrier rowTop topMem topRows mono c.conditionOrder_code) := by
  dsimp only
  exact M.structuralTrace_completeProjection t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT
    (M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace)
    c.carrier c.conditionOrder rowTop (a.actionGraph c t) alpha infinite choice nodeOrder hT2 hs hAlpha carrier
    ordinal cutOrdinal subset trace c.conditionOrder_code topMem topRows

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

theorem semanticStructuralTrace_exact_assignment_union
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
    let row := flatCarrierRow c Q B shape
    let data := flatCarrierData c Q B shape
    ∀ seq : Nat → SetMembers Q, groundSequenceGraph seq ∈ M.sets → Antitone seq →
      ∃ q : R, (∀ n, q ≤ row (seq n)) ∧ ∃ p : SetMembers Q,
        SetMembers.raw p = ZFSet.pair (c.encode q)
          (stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n)))) ∧
        (∀ n, p ≤ seq n) ∧
        SetMembers.raw (data p) = stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∧
        stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) ∈ M.sets ∧
        ∀ z, z ∈ SetMembers.raw (data p) ↔ ∃ n, z ∈ SetMembers.raw (data (seq n)) := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have unionTests := M.structuralHistory_rawTests_union t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let Q := M.refinementHistoryForcing c.carrier T stages packed
  let B := M.groundSmallSubsets (stageOneAssignments (refinementDataHistoryIndices stages packed) T) ZFSet.omega
  let shape := M.refinementHistoryForcing_shape c.carrier T stages packed
  let data := flatCarrierData c Q B shape
  dsimp only
  intro seq whole decreasing
  obtain ⟨q, belowRows, p, code, below⟩ := M.refinementHistory_lower_bound c T stages packed
    run ordinal unionTests pairing unions powers separation infinite choice carrier hT hs hPacked
    rowClosed seq whole decreasing
  have dataEqual : SetMembers.raw (data p) =
      stageOneAssignmentUnion (fun n => SetMembers.raw (data (seq n))) := by
    have coordinates := flatCarrier_coordinates c Q B shape p
    rw [code] at coordinates
    exact (ZFSet.pair_inj.1 coordinates).2.symm
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have conditionGround := M.transitive hQ (SetMembers.raw_mem p)
  rw [code] at conditionGround
  refine ⟨q, belowRows, p, code, below, dataEqual, M.pair_right conditionGround, ?_⟩
  intro z
  rw [dataEqual]
  exact mem_stageOneAssignmentUnion _ z

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

theorem semanticStructuralFairPreparation_lower_bound
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
      clockZero, birthZero, eventZero, _entries, rawSteps⟩ :=
    M.fairPreparationOrbit_conditionSequence upper pairing unions powers separation
      hQ hs hU hE0 omega whole orbitFunction selected p e initial steps
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
    rawSteps, limit, below, dataEqual, unionGround, exactEntries, ?_⟩
  intro x member
  exact M.fairRefinementSequence_assignment_prepared c T stages packed run.carriers.data
    enumFunction enumSelected seq decreasing clocks births events e initialChosen clockZero birthZero
    rawSteps x (dataEqual ▸ member)

end PartitionPilot.Forcing.TransitiveGround

end OAI
