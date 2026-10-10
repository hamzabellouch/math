import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticPreparedWitnessSelections
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparedSelectionProfiles

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

theorem semanticStructuralTrace_preparedProfileSelection
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let L := ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)
    ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
      selections ⊆ M.preparedWitnessSelections c.carrier T stages packed b.carrier (ZFSet.pair row A) A ∧
      relationImage A L selections ∈ M.sets ∧ M.groundEmbeddable (relationImage A L selections) ZFSet.omega ∧
      let Profiles := M.preparedSelectionProfiles A stages Q b.carrier T selections
      Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
      (∀ F ∈ Profiles, MeetFilterCode b.carrier b.conditionOrder
        (canonicalMeetGraph b.carrier b.conditionOrder) F) ∧
      ∀ x alpha sourceRow sourceA k enumerations z F B f,
        ZFSet.pair x (ZFSet.pair alpha
          (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈ selections →
        ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k → F ∈ Profiles := by
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall⟩ :=
    M.semanticStructuralTrace_preparedWitnessSelection c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace infinite choice condition prepared
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  refine ⟨selections, whole, function, selected, rangeGround, rangeSmall, ?_⟩
  apply M.preparedSelectionProfiles_ground_countable pairing unions powers separation collection
    infinite choice carrier hT hs hPacked nodes (run).carriers.data selected rangeGround rangeSmall
  intro alpha fields stored
  exact M.semanticStructuralTrace_storedPreparation_request_bounds c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice alpha fields stored

end PartitionPilot.Forcing.TransitiveGround

end OAI
