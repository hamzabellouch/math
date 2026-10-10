import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStructuralForcingHistoryConstruction

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 stages history : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
variable (witnesses : ∀ level P order top action,
  ZFSet.pair level (forcingStageCode P order top action) ∈ history →
    RawRefinementStageWitness M t b d base directed T T2 level P order top action)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
include pairing unions powers separation collection group nodes supports hHistory hT witnesses

theorem structuralHistory_rawTests_mono :
    ∀ level (data : Fin 15 → ZFSet.{u}), ZFSet.pair level (refinementFormulaDataCode data) ∈ packed →
      ∀ A lower stronger, stageOneRawTests M data A lower →
        ZFSet.pair stronger lower ∈ data 8 → stageOneRawTests M data A stronger := by
  intro level data entry A lower stronger tests below
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history data entry
  have ground := M.forcingStageCode_fields
    (M.transitive (M.union_mem unions (M.union_mem unions hHistory))
      (pair_second_mem_doubleUnion stored))
  exact (witnesses level P order top action stored).rawTests_order_mono
    pairing unions powers separation collection ground.1 group nodes ground.2.1 supports hT
    A lower stronger tests below

theorem structuralTrace_completeProjection
    (rows rowOrder rowTop rowAction alpha : ZFSet.{u})
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (nodeOrder : b.conditionOrder ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hStages : stages ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hRows : rows ∈ M.sets)
    (ordinal : ordinalSetProperty stages) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
    (trace : OrdinalRecursionTrace (fun level prior stage =>
      stage = M.structuralForcingStage rows rowOrder rowTop rowAction t.carrier b.carrier b.conditionOrder
        (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (rowOrderLaw : PartialOrderCode rows rowOrder) (topMem : rowTop ∈ rows)
    (topRows : ∀ row ∈ rows, ZFSet.pair row rowTop ∈ rowOrder) :
    let run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction t.carrier b.carrier
      b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
    let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
      pairing unions powers separation collection group nodes supports hHistory hT witnesses
    let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hStages (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
    letI := M.refinementHistoryPartialOrder rowOrderLaw T stages packed
    letI := M.refinementHistoryPartialOrder rowOrderLaw T alpha (graphRestriction alpha packed)
    CompleteProjection (run.restriction ordinal cutOrdinal subset rowOrderLaw)
      (run.inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
        hStages hPacked hT hAlpha hRows rowTop topMem topRows mono rowOrderLaw) := by
  dsimp only
  exact (M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction t.carrier b.carrier
    b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace).completeProjection
    ordinal cutOrdinal subset pairing unions powers separation infinite choice hStages _ hT hAlpha hRows
    rowTop topMem topRows
    (M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
      pairing unions powers separation collection group nodes supports hHistory hT witnesses) rowOrderLaw

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
