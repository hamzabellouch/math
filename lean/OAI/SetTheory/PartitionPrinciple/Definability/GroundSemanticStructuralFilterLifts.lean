import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticFairPreparationLimits
import OAI.SetTheory.PartitionPrinciple.Forcing.CompleteProjectionFilterLifts

namespace OAI

section

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

theorem semanticStructuralTrace_sameFilter_lift
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
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 ordinal trace
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    let restriction := run.restriction ordinal cutOrdinal subset c.conditionOrder_code
    let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice
    ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed)))
      (p : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)) (_hp : H.mem p)
      (q : SetMembers (M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)))
      (_hq : (projection.projectedFilter H).mem q)
      (row A : ZFSet.{u}) (_code : SetMembers.raw p = ZFSet.pair row A),
      ∃ (r : SetMembers (M.refinementHistoryForcing c.carrier T stages packed))
        (newRow newA : ZFSet.{u}), H.mem r ∧ r ≤ p ∧ restriction r ≤ q ∧
        SetMembers.raw r = ZFSet.pair newRow newA ∧
        ZFSet.pair newRow row ∈ c.conditionOrder ∧ A ⊆ newA ∧
        SetMembers.raw (restriction r) = ZFSet.pair newRow
          (assignmentCut (refinementDataHistoryLevels stages packed T) alpha newA) := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let instHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let instRestrictedHistoryOrder :=
    M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let restriction := run.restriction ordinal cutOrdinal subset c.conditionOrder_code
  let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice
  dsimp only
  intro H p hp q hq row A code
  obtain ⟨r, member, below, projected⟩ := projection.exists_mem_below_projected H p hp q hq
  obtain ⟨newRow, _, newA, _, raw⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed (SetMembers.raw_mem r))
  have belowRaw : ZFSet.pair (SetMembers.raw r) (SetMembers.raw p) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := below
  rw [raw, code] at belowRaw
  have fields := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    newRow newA row A).1 belowRaw
  exact ⟨r, newRow, newA, member, below, projected, raw, fields.2.2.1, fields.2.2.2,
    run.restrictionFunction_raw ordinal cutOrdinal subset r newRow newA raw⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
