import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralRequestBatches
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPreparedWitnessSelections

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

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "levels" => refinementDataHistoryLevels stages packed T
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "pi" => RecursiveRefinementOrderHistory.restrictionFunction run ordinal cutOrdinal subset
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace hAlpha cutOrdinal subset
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "inc" => RecursiveRefinementOrderHistory.inclusionFunction run ordinal cutOrdinal subset
  pairing unions powers separation infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono

include infinite choice
theorem semanticStructuralPreparationWitness_bounds :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    Q ∈ M.sets ∧ M.preparationWitnessBound b.carrier T Q ∈ M.sets ∧
      LQ ⊆ Q ∧ M.niceSupportNameCodes lowerAct (SetMembers.presentation LQ) T d.principalFix ⊆
        M.groundRelations T Q := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have inside : LQ ⊆ Q := by
    intro x hx
    have included := SetMembers.raw_mem (inc (SetMembers.ofMem x hx))
    rw [(run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation
      infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono] at included
    simpa only [SetMembers.raw_ofMem] using included
  exact ⟨hQ, M.preparationWitnessBound_mem pairing unions powers separation nodes hT hQ omega,
    inside, M.niceSupportNameCodes_subset_groundRelations lowerAct (SetMembers.presentation LQ)
      T d.principalFix inside⟩

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

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "levels" => refinementDataHistoryLevels stages packed T
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "pi" => RecursiveRefinementOrderHistory.restrictionFunction run ordinal cutOrdinal subset
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace hAlpha cutOrdinal subset
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "inc" => RecursiveRefinementOrderHistory.inclusionFunction run ordinal cutOrdinal subset
  pairing unions powers separation infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono

include infinite choice
theorem semanticStructuralPreparationWitness_mem :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
    ∀ A r k enumerations : ZFSet.{u},
    let selected := assignmentOnIndices indices T A
    let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
    let localBound := M.groundRelations T lower.carrier
    let J := relationImage selected localBound (graphs 0) ∪ relationImage selected localBound (graphs 1);
      r ∈ Q → k ∈ M.sets → enumerations ∈ M.sets →
      ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
        (M.niceSupportNameCodes lowerAct lower T d.principalFix)) k →
      ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
        (M.niceSupportNameCodes lowerAct lower T d.principalFix)) enumerations →
      ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound b.carrier T Q := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
  dsimp only
  intro A r k enumerations hr hk he certificates enumerated
  have bounds := M.semanticStructuralPreparationWitness_bounds c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice
  apply M.nicePreparationWitness_mem lowerAct lower T d.principalFix bounds.2.2.1
    (fun _ member => ?_) hr hk he certificates enumerated
  rcases ZFSet.mem_union.1 member with first | second
  · exact (mem_relationImage _ _ _ _).1 first |>.1
  · exact (mem_relationImage _ _ _ _).1 second |>.1

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

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 alpha history)
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_storedPreparationFamily_act_support
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (meetGraph : ZFSet.{u}) (meet : MeetOrderCode b.carrier b.conditionOrder meetGraph)
    {A k enums S : ZFSet.{u}} (hA : A ∈ M.sets)
    (hk : k ∈ M.sets) (hEnums : enums ∈ M.sets) (hS : S ∈ M.sets)
    (supportNodes : S ⊆ b.carrier) (small : M.groundEmbeddable S ZFSet.omega)
    (supportBound : certificateUsedSupports b.carrier k ⊆ S)
    (p : SetMembers Q) (g : G) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    let W := M.groundRelations T upperQ
    let N := M.groundRelations T lower.carrier
    let validN : ∀ z ∈ N, IsName lower z := fun z hz =>
      Name.isName_of_subset valid ((M.mem_groundRelations T lower.carrier z).1 hz).2
    let J := M.storedPreparationRequests A (M.refinementLevelFormulaData act lower b d alpha T T2 valid)
    let C := M.supportedEqualityCertificateBound b.carrier W
    let E := M.synchronizedEnumerationBound b.carrier W
    PreparedCertificateFamilyCode M lower.carrier lower.conditionOrder (lower.encode p)
      b.carrier b.conditionOrder meetGraph N
      (M.niceVisibilityGraph act lower b T d.principalFix) (lower.encode ⊤) ZFSet.omega J C E k enums →
    let keyMap := Name.renameFamilyGraph lower ((act).iso g) N validN
    let nodeMap := b.graph b (d.iso g)
    let tupleMap := preparationTupleActionGraph C E b.carrier N nodeMap keyMap
    let movedK := preparationFamilyFirst J N C E keyMap tupleMap k enums
    let movedEnums := preparationFamilySecond J N C E keyMap tupleMap k enums
    let movedS := relationImage S b.carrier nodeMap
    let movedA := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A
    W ∈ M.sets ∧ N ⊆ W ∧ movedK ∈ M.sets ∧ movedEnums ∈ M.sets ∧ movedS ∈ M.sets ∧
      movedS ⊆ b.carrier ∧ M.groundEmbeddable movedS ZFSet.omega ∧
      PreparedCertificateFamilyCode M lower.carrier lower.conditionOrder (lower.encode ((act).iso g p))
        b.carrier b.conditionOrder meetGraph N
        (M.niceVisibilityGraph act lower b T d.principalFix) (lower.encode ⊤) ZFSet.omega
        (M.storedPreparationRequests movedA (M.refinementLevelFormulaData act lower b d alpha T T2 valid))
        C E movedK movedEnums ∧
      certificateUsedSupports b.carrier movedK =
        relationImage (certificateUsedSupports b.carrier k) b.carrier nodeMap ∧
      certificateUsedSupports b.carrier movedK ⊆ movedS := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let upperQ := M.refinementHistoryForcing c.carrier T stages packed
  let W := M.groundRelations T upperQ
  let N := M.groundRelations T lower.carrier
  dsimp only
  intro family
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have fields : ∀ j, M.refinementLevelFormulaData act lower b d alpha T T2 valid j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem _ (M.transitive
      (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion entry))
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hGraph : (act).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    have ground := M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh omega
    unfold structuralForcingCarrier at ground
    rw [M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset] at ground
    exact ground
  have maps := M.conditionMapFamily_mem_of_actionGraph act lower t pairing unions powers separation
    collection hQ group hGraph
  obtain ⟨stage, stored⟩ := trace.1.total member
  have same := (trace.2 alpha member stage stored).trans
    (M.semanticStructuralPrefix_stageCode c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hh ordinal trace hAlpha cutOrdinal subset)
  have exactStored : ZFSet.pair alpha
      (forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t))
      ∈ history := same ▸ stored
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨_, closed, _⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  obtain ⟨validSecond, closedSecond, _⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T2 valid2 closed2 symmetric2
  have bounds := M.semanticStructuralPreparationWitness_bounds c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice
  have hW : W ∈ M.sets := M.groundRelations_mem pairing unions powers separation hT bounds.1
  have localBound : N ⊆ W := M.groundRelations_mono (fun _ h => h) bounds.2.2.1
  refine ⟨hW, localBound, ?_⟩
  exact M.storedPreparationFamily_structural_act_support act lower b d alpha T T2 valid validSecond t
    pairing unions powers separation collection fields maps nodeMaps group supports omega closed closedSecond
    hAlpha hT2 trace.1 exactStored meetGraph meet hA hW hk hEnums hS localBound supportNodes small
    p g family supportBound

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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace

theorem semanticStructuralSupportPreparedCondition_act
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S : ZFSet.{u}} (hS : S ∈ M.sets) (supportNodes : S ⊆ b.carrier)
    (small : M.groundEmbeddable S ZFSet.omega) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    ∀ (g : G) (p : SetMembers Q),
      StoredSupportPreparedConditionCode M c.carrier T stages packed b.carrier (SetMembers.raw p) S →
      let movedS := relationImage S b.carrier (b.graph b (d.iso g))
      movedS ∈ M.sets ∧ movedS ⊆ b.carrier ∧ M.groundEmbeddable movedS ZFSet.omega ∧
        StoredSupportPreparedConditionCode M c.carrier T stages packed b.carrier
          (SetMembers.raw ((act).iso g p)) movedS := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  intro g p prepared
  have nodeMapGround := M.conditionMap_graph_mem d b t nodeMaps g
  have injection := b.graph_injection b (d.iso g) (d.iso g).injective
  have imageGround := M.relationImage_mem separation hS nodes nodeMapGround
  have imageNodes : relationImage S b.carrier (b.graph b (d.iso g)) ⊆ b.carrier := by
    intro z hz
    exact (mem_relationImage _ _ _ _).1 hz |>.1
  have imageSmall := M.groundEmbeddable_image pairing unions powers separation hS nodes omega
    nodeMapGround injection supportNodes small
  refine ⟨imageGround, imageNodes, imageSmall, ?_⟩
  intro movedRow movedA movedCode y member
  obtain ⟨r, A, _, pCode⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier T stages packed) (SetMembers.raw_mem p)
  have actedCode := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace g p r A pCode
  have eqA : movedA = M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
      (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A :=
    (ZFSet.pair_inj.1 (movedCode.symm.trans actedCode)).2
  subst movedA
  obtain ⟨x, hx, edge⟩ := (M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A y).1 member
  obtain ⟨alpha, hAlphaMember, oldFields, stored, _terms, _nodeCarrier, meet, environment,
      sourceRow, sourceA, hSourceA, sourceValid, sourceSubset, selected,
      k, hk, enums, he, q, hq, cut, family, supportBound⟩ := prepared (c.encode r) A pCode x hx
  have movedSelected : y ∈ assignmentOnIndices (oldFields 0) T
      (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) sourceA) := by
    obtain ⟨_, P0, order0, top0, action0, storedRaw, fieldsEq⟩ :=
      M.structuralRefinementHistory_fields t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history oldFields stored
    rw [fieldsEq] at selected ⊢
    exact M.structuralAssignmentImage_selected_edge t.carrier b.carrier b.conditionOrder
      (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 trace.1 storedRaw selected edge
  obtain ⟨_, hMovedSource, movedSourceRow, _rowMember, movedSourceValid, _rowEdge⟩ :=
    M.semanticStructuralAction_sourceCondition c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace sourceValid g
  have movedSubset := M.structuralAssignmentImage_mono t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) sourceSubset
  have hAlpha := M.transitive hs hAlphaMember
  have cutOrdinal := ordinalSetProperty_member ordinal hAlphaMember
  have alphaSubset := ordinal.1 alpha hAlphaMember
  let lowerPacked := graphRestriction alpha packed
  let LQ := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal alphaSubset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal alphaSubset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal alphaSubset
  let fields := M.refinementLevelFormulaData lowerAct lower b d alpha T T2 valid
  have canonicalStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace hAlphaMember
  have same : oldFields = fields := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique stored canonicalStored)
  subst oldFields
  let qTyped : SetMembers LQ := SetMembers.ofMem q hq
  have movedCut := M.semanticStructuralCutGraph_act c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace hAlpha cutOrdinal alphaSubset g p q hq cut
  have movedFamily := M.semanticStructuralPrefix_storedPreparationFamily_act_support c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace hAlphaMember infinite choice
    (canonicalMeetGraph b.carrier b.conditionOrder) meet hSourceA hk he hS supportNodes small supportBound
    qTyped g
  have inputFamily : PreparedCertificateFamilyCode M lower.carrier lower.conditionOrder (lower.encode qTyped)
      b.carrier b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder)
      (M.groundRelations T lower.carrier) (M.niceVisibilityGraph lowerAct lower b T d.principalFix)
      (lower.encode ⊤) ZFSet.omega (M.storedPreparationRequests sourceA fields)
      (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T Q))
      (M.synchronizedEnumerationBound b.carrier (M.groundRelations T Q)) k enums := by
    have code : lower.encode qTyped = q := SetMembers.raw_ofMem q hq
    rw [code]
    exact family
  obtain ⟨_, _, hkg, heg, _, _, _, familyG, _, supportG⟩ := movedFamily inputFamily
  exact ⟨alpha, hAlphaMember, fields, canonicalStored, rfl, rfl, meet, environment,
    movedSourceRow, _, hMovedSource, movedSourceValid, movedSubset, movedSelected,
    _, hkg, _, heg, SetMembers.raw (lowerAct.iso g qTyped), SetMembers.raw_mem _,
    movedCut.2, familyG, supportG⟩

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

theorem semanticStructuralTrace_storedPreparation_request_bounds
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (alpha : ZFSet.{u}) (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed) :
    let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    fields 10 = b.carrier ∧ fields 11 = b.conditionOrder ∧
      fields 14 ⊆ M.groundRelations T upperQ ∧
    ∀ sourceRow sourceA, ZFSet.pair sourceRow sourceA ∈ upperQ →
      M.storedPreparationRequests sourceA fields ∈ M.sets ∧
      M.groundEmbeddable (M.storedPreparationRequests sourceA fields) ZFSet.omega := by
  have member := (run).carriers.data.function.pair_source stored
  have hAlpha := M.transitive hs member
  have cutOrdinal := ordinalSetProperty_member ordinal member
  have subset := ordinal.1 alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let actual := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have actualStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
  have same : fields = actual := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique stored actualStored)
  subst fields
  have bounds := M.semanticStructuralPreparationWitness_bounds c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice
  refine ⟨rfl, rfl, M.groundRelations_mono (fun _ h => h) bounds.2.2.1, ?_⟩
  intro sourceRow sourceA condition
  have requests := M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice condition
  exact ⟨requests.2.2.2.1, requests.2.2.2.2.1⟩

theorem semanticStructuralTrace_preparedWitnessSelection
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let L := ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)
    ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
      selections ⊆ M.preparedWitnessSelections c.carrier T stages packed b.carrier (ZFSet.pair row A) A ∧
      relationImage A L selections ∈ M.sets ∧
      M.groundEmbeddable (relationImage A L selections) ZFSet.omega := by
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  apply M.exists_storedPreparedWitnessSelection pairing unions powers separation infinite choice
    carrier hT hs hPacked nodes (run).carriers.data condition prepared
  intro alpha fields stored
  exact (M.semanticStructuralTrace_storedPreparation_request_bounds c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace infinite choice alpha fields stored).2.2.1

end PartitionPilot.Forcing.TransitiveGround

end OAI
