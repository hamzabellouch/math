import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralCutActions

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

variable {stages history : ZFSet.{u}} (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
include hh ordinal trace

variable {alpha : ZFSet.{u}} (hAlpha : alpha ∈ M.sets)
variable (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_refinementObject_supports :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    ∀ (valid : ∀ z ∈ T, IsName lower z) (C : L) (triple : Fin 3 → Name lower),
      (∀ i, d.principalFix C ≤ (lowerAct).stabilizer lower (triple i)) →
      (∀ i, HereditarilySymmetric lowerAct lower
        (d.principalSupportFamily base directed) (triple i)) →
      ∀ kind : Fin 3,
        d.principalFix C ≤ (lowerAct).stabilizer lower
          (Name.refinementOutput kind T valid (triple 0) (triple 1) (triple 2)) ∧
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
          (Name.refinementOutput kind T valid (triple 0) (triple 1) (triple 2)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  obtain ⟨_, _, closed, children⟩ := M.semanticStructuralPrefixPower_family
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset 0
  dsimp only
  intro valid C triple fixed symmetric kind
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) kind
  · exact ⟨Name.refinementQuotient_support lowerAct T valid closed (triple 0) (triple 1)
      (d.principalFix C) (fixed 0) (fixed 1),
      Name.refinementQuotient_hs lowerAct T valid closed (d.principalSupportFamily base directed)
        children (triple 0) (triple 1) (symmetric 0) (symmetric 1)⟩
  · exact ⟨Name.refinementQuotient_support lowerAct T valid closed (triple 0) (triple 2)
      (d.principalFix C) (fixed 0) (fixed 2),
      Name.refinementQuotient_hs lowerAct T valid closed (d.principalSupportFamily base directed)
        children (triple 0) (triple 2) (symmetric 0) (symmetric 2)⟩
  · exact ⟨Name.refinementNaturalMap_support lowerAct T valid closed
      (triple 0) (triple 1) (triple 2) (d.principalFix C) (fixed 0) (fixed 1) (fixed 2),
      Name.refinementNaturalMap_hs lowerAct T valid closed (d.principalSupportFamily base directed)
        children (triple 0) (triple 1) (triple 2) (symmetric 0) (symmetric 1) (symmetric 2)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
