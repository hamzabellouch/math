import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAlignedLargerCutTests
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralFinalRefinements
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralRefinementObjectSupports
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementDataOutputs

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

theorem semanticStructuralPrefix_refinementOutputs :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let data := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    let graphs := fun kind => M.refinementDataOutputGraph kind data
    (∀ kind, graphs kind ∈ M.sets) ∧
      (∀ graph, ZFSet.pair alpha graph ∈ refinementDataHistoryField stages packed 12 ↔ graph = graphs 2) ∧
      ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
        refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
          M.niceRefinementIndices act lower b d alpha T T2 valid →
        ∀ kind y, ZFSet.pair
          (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) y ∈
          graphs kind ↔ y = (Name.refinementOutput kind T valid U.val Rf.val Rc.val).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let data := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have members : ∀ j, data j ∈ M.sets := M.refinementFormulaDataCode_fields_mem data
    (M.transitive (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion entry))
  refine ⟨M.refinementDataOutputGraph_mem pairing unions powers separation data members, ?_, ?_⟩
  · intro graph
    exact refinementDataHistoryField_entry (run).carriers.data.function data entry 12 graph
  · intro C E U Rf Rc inside kind y
    exact M.refinementLevelFormulaData_output_entry act lower b d alpha T T2 valid
      pairing unions powers separation collection members C E U Rf Rc inside kind y

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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

local notation "liftName" => M.semanticStructuralNameLift c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice

local notation "projection" => M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralNameLift_projected_eval :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (H : ConditionFilter (SetMembers Q)) (tau : Name (SetMembers.presentation LQ)),
      Name.eval {p | H.mem p} (liftName tau) =
        Name.eval {p | ((projection).projectedFilter H).mem p} tau := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro H tau
  exact M.semanticStructuralNameLift_eval c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice {p | H.mem p} tau

theorem semanticStructuralNameLift_symmetric :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (F : NormalSubgroupFamily G) (tau : Name (SetMembers.presentation LQ)),
      tau.val ∈ M.sets →
      HereditarilySymmetric lowerAct (SetMembers.presentation LQ) F tau →
      (liftName tau).val = tau.val ∧
      (liftName tau).val ∈ M.sets ∧
      HereditarilySymmetric upperAct (SetMembers.presentation Q) F (liftName tau) ∧
      (∀ K : Subgroup G,
        K ≤ (lowerAct).stabilizer (SetMembers.presentation LQ) tau →
        K ≤ (upperAct).stabilizer (SetMembers.presentation Q) (liftName tau)) ∧
      ∀ H : ConditionFilter (SetMembers Q),
        Name.eval {p | H.mem p} (liftName tau) =
          Name.eval {p | ((projection).projectedFilter H).mem p} tau ∧
        Name.eval {p | ((projection).projectedFilter H).mem p} tau ∈
          (M.symmetricExtension (SetMembers.presentation Q) upperAct F H).sets := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro F tau ground symmetric
  have liftedGround := M.semanticStructuralNameLift_mem c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice tau ground
  have liftedSymmetric := M.semanticStructuralNameLift_hs c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice F tau symmetric
  refine ⟨M.semanticStructuralNameLift_val c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice tau,
    liftedGround, liftedSymmetric,
    (fun K supported => M.semanticStructuralNameLift_supported c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice K tau supported), ?_⟩
  intro H
  have equal := M.semanticStructuralNameLift_projected_eval c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice H tau
  refine ⟨equal, (M.mem_symmetricExtension (SetMembers.presentation Q) upperAct F H _).2 ?_⟩
  exact ⟨liftName tau, liftedGround, liftedSymmetric, equal⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_refinementIndices (small : M.sets.Countable)
    (square : T2 = orderedPairNameFamily (ZFSet.pair rowTop ∅) T T)
    (growth : ∀ C : L, ∃ E, C < E) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
      (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
      (And.left (And.left standard)) carrier T valid1
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      (∀ i, HereditarilySymmetric upperAct (SetMembers.presentation Q)
        (d.principalSupportFamily base directed) (tau i).val) →
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∃ C E : L, base ≤ C ∧ C < E ∧
          (∀ i, d.principalFix C ≤ (upperAct).stabilizer upper (tau i).val) ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            M.niceRefinementIndices lowerAct lower b d beta T T2 validT ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          ∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
    (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
  dsimp only
  intro tau symmetric
  obtain ⟨beta, hBeta, result⟩ := M.semanticStructuralTrace_finalRefinementNames
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT small tau
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
  let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  dsimp only at result
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported, preserved⟩ := result
  obtain ⟨C, baseC, fixes⟩ := Name.exists_commonPrincipalNameSupport upperAct upper d base directed
    (fun i => (tau i).val) (fun i => (symmetric i).symmetric)
  obtain ⟨E, strict⟩ := growth C
  have member : (d.principalSupportFamily base directed).mem (d.principalFix C) :=
    (d.principalSupportFamily_basis base directed _).2 ⟨C, le_rfl⟩
  have nice := fun i => (supported (d.principalFix C) member fixes i).1
  have hLower : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have family : (normalized 3).val = Name.familySet ⊤ T ((termData 0).2 beta cutOrdinal subset) := by
    rw [normalizedLast]
    exact last
  have niceU : NiceNameCode lowerAct lower T (d.principalFix C) (normalized 0).val.val := by
    have niceZero := nice 0
    simp only [Matrix.cons_val_zero, iteratedPairNameFamily_zero] at niceZero
    exact niceZero
  have onePower : iteratedPairNameFamily (ZFSet.pair rowTop ∅) T 1 = T2 := square.symm
  have niceRf : NiceNameCode lowerAct lower T2 (d.principalFix C) (normalized 1).val.val := by
    exact (congrArg (fun S => NiceNameCode lowerAct lower S (d.principalFix C)
      (normalized 1).val.val) onePower).mp (nice 1)
  have niceRc : NiceNameCode lowerAct lower T2 (d.principalFix C) (normalized 2).val.val := by
    exact (congrArg (fun S => NiceNameCode lowerAct lower S (d.principalFix C)
      (normalized 2).val.val) onePower).mp (nice 2)
  have index := M.normalizedRefinementIndex_mem lowerAct lower b d pairing unions powers separation
    collection hLower hOrder beta T T2 ((termData 0).2 beta cutOrdinal subset)
    C E normalized family strict niceU niceRf niceRc forced
  exact ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, preserved⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_storedRefinementIndices (small : M.sets.Countable)
    (square : T2 = orderedPairNameFamily (ZFSet.pair rowTop ∅) T T)
    (growth : ∀ C : L, ∃ E, C < E) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
      (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
      (And.left (And.left standard)) carrier T valid1
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      (∀ i, HereditarilySymmetric upperAct (SetMembers.presentation Q)
        (d.principalSupportFamily base directed) (tau i).val) →
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∃ C E : L, base ≤ C ∧ C < E ∧
          (∀ i, d.principalFix C ≤ (upperAct).stabilizer upper (tau i).val) ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            M.niceRefinementIndices lowerAct lower b d beta T T2 validT ∧
          ZFSet.pair beta (M.niceRefinementIndices lowerAct lower b d beta T T2 validT) ∈
            refinementDataHistoryField K packed 0 ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            refinementDataHistoryIndices K packed ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          ∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
    (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
  dsimp only
  intro tau symmetric
  obtain ⟨beta, hBeta, result⟩ := M.semanticStructuralTrace_refinementIndices
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT small
    square growth tau symmetric
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  dsimp only at result
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, preserved⟩ := result
  have stored := (M.semanticStructuralPrefix_indexField_entry
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hBeta _).2 rfl
  have attained := M.semanticStructuralPrefix_index_mem_history
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hBeta _ index
  exact ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, stored, attained, preserved⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_refinementOutputs (small : M.sets.Countable)
    (square : T2 = orderedPairNameFamily (ZFSet.pair rowTop ∅) T T)
    (growth : ∀ C : L, ∃ E, C < E) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
      (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
      (And.left (And.left standard)) carrier T valid1
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      (∀ i, HereditarilySymmetric upperAct (SetMembers.presentation Q)
        (d.principalSupportFamily base directed) (tau i).val) →
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∃ C E : L, base ≤ C ∧ C < E ∧
          (∀ i, d.principalFix C ≤ (upperAct).stabilizer upper (tau i).val) ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            M.niceRefinementIndices lowerAct lower b d beta T T2 validT ∧
          ZFSet.pair beta (M.niceRefinementIndices lowerAct lower b d beta T T2 validT) ∈
            refinementDataHistoryField K packed 0 ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            refinementDataHistoryIndices K packed ∧
          (Name.refinementQuotient T validT (normalized 0).val (normalized 1).val).val ∈ M.sets ∧
          (Name.refinementQuotient T validT (normalized 0).val (normalized 2).val).val ∈ M.sets ∧
          (Name.refinementNaturalMap T validT (normalized 0).val (normalized 1).val
            (normalized 2).val).val ∈ M.sets ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          (∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val) ∧
          RefinementObjectValues {p | (projection.projectedFilter H).mem p} T validT
            (normalized 0).val (normalized 1).val (normalized 2).val ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementQuotient T validT (normalized 0).val (normalized 1).val) =
            equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 1).val) ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementQuotient T validT (normalized 0).val (normalized 2).val) =
            equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 2).val) ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementNaturalMap T validT (normalized 0).val (normalized 1).val (normalized 2).val) =
            refinementQuotientMap (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 1).val) (Name.eval {p | H.mem p} (tau 2).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
    (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
  dsimp only
  intro tau symmetric
  obtain ⟨beta, hBeta, result⟩ := M.semanticStructuralTrace_storedRefinementIndices
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT small
    square growth tau symmetric
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
  dsimp only at result
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, stored, attained, preserved⟩ := result
  have hLower : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have family : (normalized 3).val = Name.familySet ⊤ T ((termData 0).2 beta cutOrdinal subset) := by
    rw [normalizedLast]
    exact last
  obtain ⟨fineGround, coarseGround, mapGround, outputValues⟩ := M.normalizedRefinementOutputs
    lower pairing unions powers separation collection hLower hOrder T hT
    ((termData 0).2 beta cutOrdinal subset) normalized family forced
  refine ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, stored, attained, fineGround, coarseGround, mapGround, ?_⟩
  intro H upperGeneric lowerCoded lowerGeneric originalValid
  have same := preserved H upperGeneric lowerCoded lowerGeneric originalValid
  have values := outputValues _ lowerGeneric
  refine ⟨same, values, ?_, ?_, ?_⟩
  · exact values.fine_quotient.trans (congrArg₂ equivalenceClasses (same 0) (same 1))
  · exact values.coarse_quotient.trans (congrArg₂ equivalenceClasses (same 0) (same 2))
  · exact values.natural_map.trans
      ((congrArg₂ (fun U R => refinementQuotientMap U R _) (same 0) (same 1)).trans
        (congrArg (refinementQuotientMap _ _) (same 2)))

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_storedRefinementOutputs (small : M.sets.Countable)
    (square : T2 = orderedPairNameFamily (ZFSet.pair rowTop ∅) T T)
    (growth : ∀ C : L, ∃ E, C < E) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
      (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
      (And.left (And.left standard)) carrier T valid1
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      (∀ i, HereditarilySymmetric upperAct (SetMembers.presentation Q)
        (d.principalSupportFamily base directed) (tau i).val) →
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∃ C E : L, base ≤ C ∧ C < E ∧
          (∀ i, d.principalFix C ≤ (upperAct).stabilizer upper (tau i).val) ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            M.niceRefinementIndices lowerAct lower b d beta T T2 validT ∧
          ZFSet.pair beta (M.niceRefinementIndices lowerAct lower b d beta T T2 validT) ∈
            refinementDataHistoryField K packed 0 ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            refinementDataHistoryIndices K packed ∧
          (Name.refinementQuotient T validT (normalized 0).val (normalized 1).val).val ∈ M.sets ∧
          (Name.refinementQuotient T validT (normalized 0).val (normalized 2).val).val ∈ M.sets ∧
          (Name.refinementNaturalMap T validT (normalized 0).val (normalized 1).val
            (normalized 2).val).val ∈ M.sets ∧
        ∃ outputGraphs : Fin 3 → ZFSet,
          (∀ kind, outputGraphs kind ∈ M.sets) ∧
          ZFSet.pair beta (outputGraphs 2) ∈ refinementDataHistoryField K packed 12 ∧
          (∀ kind y, ZFSet.pair
            (refinementIndexCode beta (b.encode C) (b.encode E)
              (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val) y ∈
                outputGraphs kind ↔
            y = (Name.refinementOutput kind T validT
              (normalized 0).val (normalized 1).val (normalized 2).val).val) ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          (∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val) ∧
          RefinementObjectValues {p | (projection.projectedFilter H).mem p} T validT
            (normalized 0).val (normalized 1).val (normalized 2).val ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementQuotient T validT (normalized 0).val (normalized 1).val) =
            equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 1).val) ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementQuotient T validT (normalized 0).val (normalized 2).val) =
            equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 2).val) ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementNaturalMap T validT (normalized 0).val (normalized 1).val (normalized 2).val) =
            refinementQuotientMap (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 1).val) (Name.eval {p | H.mem p} (tau 2).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
    (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
  dsimp only
  intro tau symmetric
  obtain ⟨beta, hBeta, result⟩ := M.semanticStructuralTrace_refinementOutputs
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT small
    square growth tau symmetric
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
  let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  let validT := (termData 0).2 beta cutOrdinal subset
  let data := M.refinementLevelFormulaData lowerAct lower b d beta T T2 validT
  let graphs := fun kind => M.refinementDataOutputGraph kind data
  dsimp only at result
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, stored, attained, fineGround, coarseGround,
    mapGround, preserved⟩ := result
  have aligned := M.semanticStructuralPrefix_refinementOutputs c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hBeta
  refine ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, stored, attained, fineGround, coarseGround, mapGround,
    graphs, aligned.1, (aligned.2.1 _).2 rfl, ?_, preserved⟩
  exact aligned.2.2 C E (normalized 0) (normalized 1) (normalized 2) index

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_symmetricRefinementOutputs (small : M.sets.Countable)
    (square : T2 = orderedPairNameFamily (ZFSet.pair rowTop ∅) T T)
    (growth : ∀ C : L, ∃ E, C < E) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
      (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
      (And.left (And.left standard)) carrier T valid1
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      (∀ i, HereditarilySymmetric upperAct (SetMembers.presentation Q)
        (d.principalSupportFamily base directed) (tau i).val) →
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∃ C E : L, base ≤ C ∧ C < E ∧
          (∀ i, d.principalFix C ≤ (upperAct).stabilizer upper (tau i).val) ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            M.niceRefinementIndices lowerAct lower b d beta T T2 validT ∧
          ZFSet.pair beta (M.niceRefinementIndices lowerAct lower b d beta T T2 validT) ∈
            refinementDataHistoryField K packed 0 ∧
          refinementIndexCode beta (b.encode C) (b.encode E)
            (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val ∈
            refinementDataHistoryIndices K packed ∧
          (Name.refinementQuotient T validT (normalized 0).val (normalized 1).val).val ∈ M.sets ∧
          (Name.refinementQuotient T validT (normalized 0).val (normalized 2).val).val ∈ M.sets ∧
          (Name.refinementNaturalMap T validT (normalized 0).val (normalized 1).val
            (normalized 2).val).val ∈ M.sets ∧
        ∃ outputGraphs : Fin 3 → ZFSet,
          (∀ kind, outputGraphs kind ∈ M.sets) ∧
          ZFSet.pair beta (outputGraphs 2) ∈ refinementDataHistoryField K packed 12 ∧
          (∀ kind y, ZFSet.pair
            (refinementIndexCode beta (b.encode C) (b.encode E)
              (normalized 0).val.val (normalized 1).val.val (normalized 2).val.val) y ∈
                outputGraphs kind ↔
            y = (Name.refinementOutput kind T validT
              (normalized 0).val (normalized 1).val (normalized 2).val).val) ∧
        let outputs := fun kind => Name.refinementOutput kind T validT
          (normalized 0).val (normalized 1).val (normalized 2).val
        let liftedOutputs := fun kind => Name.rename upper inc (outputs kind)
        (∀ kind : Fin 3,
          d.principalFix C ≤ lowerAct.stabilizer lower (outputs kind) ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed) (outputs kind) ∧
          (liftedOutputs kind).val = (outputs kind).val ∧
          (liftedOutputs kind).val ∈ M.sets ∧
          d.principalFix C ≤ (upperAct).stabilizer upper (liftedOutputs kind) ∧
          HereditarilySymmetric upperAct upper (d.principalSupportFamily base directed) (liftedOutputs kind)) ∧
        (∀ (H : ConditionFilter (SetMembers Q)) (kind : Fin 3),
          Name.eval {p | H.mem p} (liftedOutputs kind) =
            Name.eval {p | (projection.projectedFilter H).mem p} (outputs kind) ∧
          Name.eval {p | (projection.projectedFilter H).mem p} (outputs kind) ∈
            (M.symmetricExtension upper upperAct (d.principalSupportFamily base directed) H).sets) ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          (∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val) ∧
          RefinementObjectValues {p | (projection.projectedFilter H).mem p} T validT
            (normalized 0).val (normalized 1).val (normalized 2).val ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementQuotient T validT (normalized 0).val (normalized 1).val) =
            equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 1).val) ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementQuotient T validT (normalized 0).val (normalized 2).val) =
            equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 2).val) ∧
          Name.eval {p | (projection.projectedFilter H).mem p}
            (Name.refinementNaturalMap T validT (normalized 0).val (normalized 1).val (normalized 2).val) =
            refinementQuotientMap (Name.eval {p | H.mem p} (tau 0).val)
              (Name.eval {p | H.mem p} (tau 1).val) (Name.eval {p | H.mem p} (tau 2).val) ∧
          equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 1).val) ∈
              (M.symmetricExtension upper upperAct (d.principalSupportFamily base directed) H).sets ∧
          equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 2).val) ∈
              (M.symmetricExtension upper upperAct (d.principalSupportFamily base directed) H).sets ∧
          refinementQuotientMap (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 1).val) (Name.eval {p | H.mem p} (tau 2).val) ∈
              (M.symmetricExtension upper upperAct (d.principalSupportFamily base directed) H).sets := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
    (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
  dsimp only
  intro tau symmetric
  obtain ⟨beta, hBeta, result⟩ := M.semanticStructuralTrace_storedRefinementOutputs
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT small
    square growth tau symmetric
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
  let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  let validT := (termData 0).2 beta cutOrdinal subset
  let upper := SetMembers.presentation Q
  let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
    pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
  dsimp only at result
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, stored, attained, fineGround, coarseGround,
    mapGround, outputGraphs, graphsGround, graphStored, graphEntries, preserved⟩ := result
  let triple := fun i : Fin 3 => (normalized i.castSucc).val
  have supportedTriple := supported (d.principalFix C) ⟨C, le_refl _⟩ fixes
  have inputSupport : ∀ i, d.principalFix C ≤ lowerAct.stabilizer lower (triple i) := by
    intro i
    exact ((niceNameCode_iff lowerAct lower (triple i)).1 (supportedTriple i).1).2
  have inputHS : ∀ i, HereditarilySymmetric lowerAct lower
      (d.principalSupportFamily base directed) (triple i) := fun i => (supportedTriple i).2
  let outputs := fun kind => Name.refinementOutput kind T validT
    (normalized 0).val (normalized 1).val (normalized 2).val
  let liftedOutputs := fun kind => Name.rename upper inc (outputs kind)
  have outputSupport := M.semanticStructuralPrefix_refinementObject_supports
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset
    validT C triple inputSupport inputHS
  have outputGround : ∀ kind : Fin 3, (outputs kind).val ∈ M.sets := by
    intro kind
    refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) kind
    · exact fineGround
    · exact coarseGround
    · exact mapGround
  have lifted := fun kind : Fin 3 => M.semanticStructuralNameLift_symmetric
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset
    infinite choice (d.principalSupportFamily base directed) (outputs kind) (outputGround kind)
      (outputSupport kind).2
  refine ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported,
    C, E, baseC, strict, fixes, index, stored, attained, fineGround, coarseGround, mapGround,
    outputGraphs, graphsGround, graphStored, graphEntries, ?_, ?_, ?_⟩
  · intro kind
    exact ⟨(outputSupport kind).1, (outputSupport kind).2, (lifted kind).1,
      (lifted kind).2.1, (lifted kind).2.2.2.1 _ (outputSupport kind).1, (lifted kind).2.2.1⟩
  · intro H kind
    exact (lifted kind).2.2.2.2 H
  · intro H generic coded ordinary validity
    obtain ⟨same, objects, fine, coarse, natural⟩ := preserved H generic coded ordinary validity
    refine ⟨same, objects, fine, coarse, natural, ?_, ?_, ?_⟩
    · exact fine ▸ ((lifted 0).2.2.2.2 H).2
    · exact coarse ▸ ((lifted 1).2.2.2.2 H).2
    · exact natural ▸ ((lifted 2).2.2.2.2 H).2

end PartitionPilot.Forcing.TransitiveGround

end OAI
