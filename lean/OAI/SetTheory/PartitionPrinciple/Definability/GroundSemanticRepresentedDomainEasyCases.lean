import OAI.SetTheory.PartitionPrinciple.Forcing.GroundOrdinaryEqualityDecisionFusion
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableRowSequenceReflection

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open scoped ZFSet
universe u
private theorem decoded_property_congr
    {G R : Type u} [Group G] [PartialOrder R]
    (M : TransitiveGround.{u}) (c : Presentation R) (t : Presentation G)
    (T alpha rowGraph packed1 packed2 assignments1 assignments2 action1 action2 : ZFSet.{u})
    (packedEq : packed1 = packed2) (assignmentsEq : assignments1 = assignments2)
    (actionEq : action1 = action2)
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop)
    (code1 : letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1
      let Q1 := M.refinementHistoryForcing c.carrier T alpha packed1
      PosetActionCode t.carrier Q1 ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
        (SetMembers.presentation Q1).conditionOrder
        (rawRowAssignmentActionGraph t.carrier Q1 c.carrier (⋃₀ ⋃₀ Q1) assignments1 rowGraph action1))
    (code2 : letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2
      let Q2 := M.refinementHistoryForcing c.carrier T alpha packed2
      PosetActionCode t.carrier Q2 ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
        (SetMembers.presentation Q2).conditionOrder
        (rawRowAssignmentActionGraph t.carrier Q2 c.carrier (⋃₀ ⋃₀ Q2) assignments2 rowGraph action2)) :
    Property (M.refinementHistoryForcing c.carrier T alpha packed1)
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1)
      (letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1
       code1.toPresentedPosetAction t (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha packed1))) ↔
    Property (M.refinementHistoryForcing c.carrier T alpha packed2)
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2)
      (letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2
       code2.toPresentedPosetAction t (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha packed2))) := by
  subst packed2
  subst assignments2
  subst action2
  rfl

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

variable {stages history alpha : ZFSet.{u}} (hh : history ∈ M.sets)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
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
include hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_restricted_property
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop) :
    Property
      (M.refinementHistoryForcing c.carrier T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha (graphRestriction alpha history)))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha (graphRestriction alpha history)))
      (M.semanticStructuralAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
        cutOrdinal (trace.restrict cutOrdinal subset)) ↔
    Property Q (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked)
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset) := by
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  unfold semanticStructuralAction semanticStructuralPrefixAction
  exact decoded_property_congr M c t T alpha (a.actionGraph c t) _ _ _ _ _ _ packedEq
    (M.structuralAssignments_history_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 alpha history)
    (M.structuralAssignmentActionGraph_history_restrict t.carrier b.carrier b.conditionOrder
      (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history)
    Property _ _

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open scoped ZFSet
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

variable {stages history alpha : ZFSet.{u}} (hh : history ∈ M.sets)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
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
include hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_subhistory_property
    {gamma : ZFSet.{u}} (hGamma : gamma ∈ M.sets) (gammaOrdinal : ordinalSetProperty gamma)
    (alphaGamma : alpha ⊆ gamma) (gammaSubset : gamma ⊆ stages)
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop) :
    let historyGamma := graphRestriction gamma history
    let hhGamma := M.graphRestriction_mem unions separation hGamma hh
    let traceGamma := trace.restrict gammaOrdinal gammaSubset
    let packedGamma := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 gamma historyGamma
    Property (M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packedGamma))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packedGamma))
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hhGamma traceGamma hAlpha cutOrdinal alphaGamma) ↔
    Property Q (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked)
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset) := by
  dsimp only
  have inner := M.semanticStructuralPrefixAction_restricted_property c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows (M.graphRestriction_mem unions separation hGamma hh)
    (trace.restrict gammaOrdinal gammaSubset) hAlpha cutOrdinal alphaGamma Property
  have outer := M.semanticStructuralPrefixAction_restricted_property c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset Property
  let Step := fun level prior stage => stage =
    M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 level prior
  let Applied := fun (h : ZFSet.{u}) (ground : h ∈ M.sets)
      (tr : OrdinalRecursionTrace Step alpha h) =>
    Property (M.refinementHistoryForcing c.carrier T alpha
      (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 alpha h))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha h))
      (M.semanticStructuralAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hAlpha ground cutOrdinal tr)
  have congruent (h1 h2 : ZFSet.{u}) (equal : h1 = h2)
      (ground1 : h1 ∈ M.sets) (ground2 : h2 ∈ M.sets)
      (trace1 : OrdinalRecursionTrace Step alpha h1) (trace2 : OrdinalRecursionTrace Step alpha h2) :
      Applied h1 ground1 trace1 ↔ Applied h2 ground2 trace2 := by
    subst h2
    rfl
  have aligned := congruent _ _ (graphRestriction_restrict alphaGamma)
    (M.graphRestriction_mem unions separation hAlpha (M.graphRestriction_mem unions separation hGamma hh))
    (M.graphRestriction_mem unions separation hAlpha hh)
    ((trace.restrict gammaOrdinal gammaSubset).restrict cutOrdinal alphaGamma)
    (trace.restrict cutOrdinal subset)
  exact inner.symm.trans (aligned.trans outer)

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open scoped ZFSet
universe u
section Core
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

private theorem domain_decisions_of_row_closed
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid →
      ∀ u : Name lower, u.val ∈ T →
      ∃ pCut r : SetMembers Q,
        lower.encode pCut = ZFSet.pair row (assignmentCut
          (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
        ((∀ q, q ≤ r → ¬ Name.ForcesMem q u U.val) ∨
          (Name.ForcesMem r u U.val ∧
            ((∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A ∧
              Name.ForcesEq r (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v)) ∨
            (∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
              ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v))))) := by
  classical
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  dsimp only
  intro C E U Rf Rc idx u hu
  let pCut : SetMembers Q := SetMembers.ofMem
    (ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A))
    ((run).carriers.cut_mem condition member)
  have cutCode : lower.encode pCut =
      ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A) :=
    SetMembers.raw_ofMem _ _
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
  have lowerCarrier : lower.carrier ∈ M.sets := fields 7
  have lowerOrder : lower.conditionOrder ∈ M.sets := fields 8
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  have closedRestricted := M.semanticStructuralTrace_internally_closed c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
    nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
    cutOrdinal (trace.restrict cutOrdinal subset) infinite choice rowClosed
  dsimp only at closedRestricted
  rw [packedEq] at closedRestricted
  have closed : InternallyCountablyClosed M lower := closedRestricted
  let original : (M.nameDomain lower).names := ⟨u, M.transitive hT hu⟩
  let coarse : (M.nameDomain lower).names := ⟨Name.refinementClass T valid Rc.val u,
    M.refinementClass_mem lower pairing unions powers separation collection lowerCarrier lowerOrder
      hT valid Rc.val u Rc.property original.property⟩
  obtain ⟨activeCut, activeBelow, decided⟩ := decisionWitness_dense
    (M.nameDomain lower) (.mem 0 1) (extend original (extend U Fin.elim0)) pCut
  rcases decided with active | inactive
  · obtain ⟨_, _, families⟩ :=
      M.semanticStructuralPrefix_fixedIndexClassFamilies c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
        topMem topRows hs hh ordinal trace member infinite choice condition C E U Rf Rc idx
    obtain ⟨_, _, wholeImage, smallImage, validImage, imageEntry, _⟩ := families 0
    obtain ⟨r, belowActive, _, decisions⟩ := M.ordinaryEqualityDecisions_simultaneous_dense lower
      pairing unions powers separation collection infinite choice lowerCarrier lowerOrder
      wholeImage smallImage validImage closed coarse activeCut activeCut le_rfl
    refine ⟨pCut, r, cutCode, belowActive.trans activeBelow, Or.inr
      ⟨Name.forcesMem_mono active belowActive, ?_⟩⟩
    by_cases reuse : ∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
        stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
          U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A ∧
        Name.ForcesEq r (Name.refinementClass T valid Rc.val u)
          (Name.refinementClass T valid Rc.val v)
    · exact Or.inl reuse
    · refine Or.inr ?_
      intro v w hv hw old q below equal
      have inImage := (imageEntry (Name.refinementClass T valid Rc.val v).val).2
        ⟨v, w, hv, hw, old, rfl⟩
      let previous : (M.nameDomain lower).names :=
        ⟨Name.refinementClass T valid Rc.val v, M.transitive wholeImage inImage⟩
      rcases decisions previous inImage with positive | negative
      · exact reuse ⟨v, w, hv, hw, old, Name.forcesEq_symm positive⟩
      · exact negative q below (Name.forcesEq_symm equal)
  · exact ⟨pCut, activeCut, cutCode, activeBelow, Or.inl inactive⟩

end Core

variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem semanticStructuralSuccessor_domain_decisions
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u}),
      ∀ (rowAction : a.actionGraph c t ∈ M.sets)
        (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
        (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
        (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
        (supports : supportBasisCode b t d.principalFix ∈ M.sets)
        (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
        (valid1 : ∀ z ∈ T, IsName c.pairEmpty z) (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
        (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
        (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
        (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (topMem : rowTop ∈ c.carrier)
        (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
        (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
        (ordinal : ordinalSetProperty stages)
        (trace : OrdinalRecursionTrace (fun level prior stage => stage =
          M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
            t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
            (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
        (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
        (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 ordinal trace
      let cutOrdinal := ordinalSetProperty_member ordinal member
      let subset := (And.left ordinal) alpha member
      let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      ∀ {row A : ZFSet.{u}},
      ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation Q
      let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
        cutOrdinal carrier T valid1
      let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
        valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace
        (M.transitive hs member) cutOrdinal subset
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid →
      ∀ u : Name lower, u.val ∈ T →
      ∃ pCut r : SetMembers Q,
        lower.encode pCut = ZFSet.pair row (assignmentCut
          (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
        ((∀ q, q ≤ r → ¬ Name.ForcesMem q u U.val) ∨
          (Name.ForcesMem r u U.val ∧
            ((∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A ∧
              Name.ForcesEq r (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v)) ∨
            (∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
              ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v))))) := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows stages history hs hh ordinal trace
    alpha member row A condition
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation
    infinite choice hX two
  exact domain_decisions_of_row_closed M c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier order rowAction group nodes nodeOrder nodeAction
    nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice rowClosed condition

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem semanticStructuralSuccessor_domain_decisions_lift
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u}),
      ∀ (rowAction : a.actionGraph c t ∈ M.sets)
        (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
        (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
        (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
        (supports : supportBasisCode b t d.principalFix ∈ M.sets)
        (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
        (valid1 : ∀ z ∈ T, IsName c.pairEmpty z) (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
        (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
        (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
        (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (topMem : rowTop ∈ c.carrier)
        (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
        (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
        (ordinal : ordinalSetProperty stages)
        (trace : OrdinalRecursionTrace (fun level prior stage => stage =
          M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
            t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
            (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
        (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
        (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 ordinal trace
      let cutOrdinal := ordinalSetProperty_member ordinal member
      let subset := (And.left ordinal) alpha member
      let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      ∀ {row A : ZFSet.{u}},
      ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation Q
      let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
        cutOrdinal carrier T valid1
      let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
        valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace
        (M.transitive hs member) cutOrdinal subset
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid →
      ∀ u : Name lower, u.val ∈ T →
      ∃ pCut r : SetMembers Q,
        lower.encode pCut = ZFSet.pair row (assignmentCut
          (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
        ((∀ q, q ≤ r → ¬ Name.ForcesMem q u U.val) ∨
          (Name.ForcesMem r u U.val ∧
            ((∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A ∧
              Name.ForcesEq r (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v)) ∨
            (∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
              ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v))))) ∧
        ∃ lowerRow lowerA : ZFSet.{u}, lower.encode r = ZFSet.pair lowerRow lowerA ∧
          let liftedA := assignmentSplice (refinementDataHistoryLevels stages packed T) alpha lowerA A
          ZFSet.pair lowerRow liftedA ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
          ZFSet.pair (ZFSet.pair lowerRow liftedA) (ZFSet.pair row A) ∈
            M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
          A ⊆ liftedA ∧
          ZFSet.pair lowerRow (assignmentCut (refinementDataHistoryLevels stages packed T) alpha liftedA) =
            lower.encode r := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows stages history hs hh ordinal trace
    alpha member row A condition
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
    (M.natSetCode_mem separation infinite 2)
  let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
    (M.natSetCode_mem separation infinite 2)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  intro C E U Rf Rc idx u hu
  obtain ⟨pCut, r, cutCode, below, decisions⟩ :=
    M.semanticStructuralSuccessor_domain_decisions t b d base directed
      pairing unions powers separation collection infinite choice X hX a T T2 rowTop
      rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
      valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows stages history hs hh ordinal trace alpha member condition C E U Rf Rc idx u hu
  obtain ⟨lowerRow, _, lowerA, _, rCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T alpha lowerPacked (SetMembers.raw_mem r))
  change lower.encode r = ZFSet.pair lowerRow lowerA at rCode
  change lower.encode pCut = ZFSet.pair row
    (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A) at cutCode
  have lowerBelow : ZFSet.pair (ZFSet.pair lowerRow lowerA)
      (ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T alpha lowerPacked := by
    change ZFSet.pair (lower.encode r) (lower.encode pCut) ∈ _ at below
    rwa [rCode, cutCode] at below
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  obtain ⟨lifted, extension, exactCut⟩ := historyRun.splice_lifting pairing unions powers separation
    infinite choice hs hPacked hT (M.transitive hs member) ordinal cutOrdinal subset mono condition lowerBelow
  have retained := ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    _ _ _ _).1 extension).2.2.2
  refine ⟨pCut, r, cutCode, below, decisions, lowerRow, lowerA, rCode,
    lifted, extension, retained, ?_⟩
  rw [exactCut]
  exact rCode.symm






theorem semanticStructuralSuccessor_represented_or_fresh
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u}),
      ∀ (rowAction : a.actionGraph c t ∈ M.sets)
        (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
        (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
        (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
        (supports : supportBasisCode b t d.principalFix ∈ M.sets)
        (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
        (valid1 : ∀ z ∈ T, IsName c.pairEmpty z) (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
        (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
        (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
        (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (topMem : rowTop ∈ c.carrier)
        (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
        (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
        (ordinal : ordinalSetProperty stages)
        (trace : OrdinalRecursionTrace (fun level prior stage => stage =
          M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
            t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
            (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
        (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
        (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 ordinal trace
      let cutOrdinal := ordinalSetProperty_member ordinal member
      let subset := (And.left ordinal) alpha member
      let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      ∀ {row A : ZFSet.{u}},
      ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation Q
      let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
        cutOrdinal carrier T valid1
      let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
        valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace
        (M.transitive hs member) cutOrdinal subset
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid →
      ∀ u : Name lower, ∀ (hu : u.val ∈ T),
      ∃ pCut r : SetMembers Q,
        lower.encode pCut = ZFSet.pair row (assignmentCut
          (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
        ∃ lowerRow lowerA : ZFSet.{u}, lower.encode r = ZFSet.pair lowerRow lowerA ∧
          let liftedA := assignmentSplice (refinementDataHistoryLevels stages packed T) alpha lowerA A
          ZFSet.pair lowerRow liftedA ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
          ZFSet.pair (ZFSet.pair lowerRow liftedA) (ZFSet.pair row A) ∈
            M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
          A ⊆ liftedA ∧
          ZFSet.pair lowerRow (assignmentCut (refinementDataHistoryLevels stages packed T) alpha liftedA) =
            lower.encode r ∧
          (ZFSet.pair lowerRow liftedA ∈ M.representedDomainConditions lower
            (M.refinementHistoryForcing c.carrier T stages packed)
            (refinementDataHistoryLevels stages packed T) alpha T valid
            (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
            U Rc ⟨u, M.transitive hT hu⟩ ∨
          (Name.ForcesMem r u U.val ∧
            ∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
              ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v))) := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows stages history hs hh ordinal trace
    alpha member row A condition
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
    (M.natSetCode_mem separation infinite 2)
  let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
    (M.natSetCode_mem separation infinite 2)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  intro C E U Rf Rc idx u hu
  obtain ⟨pCut, r, cutCode, below, decisions, lowerRow, lowerA, rCode,
      lifted, extension, retained, exactCut⟩ :=
    M.semanticStructuralSuccessor_domain_decisions_lift t b d base directed
      pairing unions powers separation collection infinite choice X hX a T T2 rowTop
      rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
      valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows stages history hs hh ordinal trace alpha member condition C E U Rf Rc idx u hu
  refine ⟨pCut, r, cutCode, below, lowerRow, lowerA, rCode, lifted, extension, retained, exactCut, ?_⟩
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh trace (M.transitive hs member) cutOrdinal subset
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
  have fields : ∀ j, M.refinementLevelFormulaData act lower b d alpha T T2 valid j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem _ (M.transitive
      (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion entry))
  have lowerCarrier : lower.carrier ∈ M.sets := fields 7
  have lowerOrder : lower.conditionOrder ∈ M.sets := fields 8
  have hUpper := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked
    (M.omega_mem separation infinite)
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hs hPacked hT
  have hIdx := M.refinementIndexCode_mem pairing (M.transitive hs member)
    (M.transitive nodes (b.encode_mem C)) (M.transitive nodes (b.encode_mem E)) U.property Rf.property Rc.property
  have exactEntry := M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerCarrier lowerOrder hUpper hLevels (M.transitive hs member) hT valid hIdx U Rc
    ⟨u, M.transitive hT hu⟩ lowerRow
    (assignmentSplice (refinementDataHistoryLevels stages packed T) alpha lowerA A) r exactCut.symm
  rcases decisions with inactive | ⟨active, reuse | fresh⟩
  · exact Or.inl (exactEntry.2 ⟨lifted, Or.inl inactive⟩)
  · obtain ⟨v, w, hv, hw, literal, equal⟩ := reuse
    exact Or.inl (exactEntry.2 ⟨lifted, Or.inr ⟨active, v, w, hv, hw, retained literal, equal⟩⟩)
  · exact Or.inr ⟨active, fresh⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
