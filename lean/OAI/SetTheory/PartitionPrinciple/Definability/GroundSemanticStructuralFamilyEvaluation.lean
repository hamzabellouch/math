import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralCutActions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundStructuralFinitePowerTerms

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

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem ordinal trace
local notation "projection" => M.semanticStructuralTrace_completeProjection c a t b d base directed
  T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
  nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
  symmetric1 symmetric2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralPrefixMembershipName_eval (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    let valid := (termData n).2 alpha cutOrdinal subset
    let upper := SetMembers.presentation Q
    let lower := SetMembers.presentation LQ
    ∀ (tau : (M.nameDomain upper).names) (f : ZFSet.{u}),
      ZFSet.IsFunc J (M.groundPower Q) f →
      (∀ sigma A, ZFSet.pair sigma A ∈ f →
        A ⊆ M.ordinaryMembershipDecisions Q
          (M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) sigma tau.val.val ∧
        A ⊆ LQ ∧ ∀ q ∈ LQ, ∃ p ∈ A, ∃ r ∈ LQ,
          ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha packed) ∧
          ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha packed)) →
      let N := Name.crossStageMembershipName upper lower inc J valid tau.val
      N.val ∈ M.sets ∧ ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
        ((projection).projectedFilter H).GenericFor (M.codedFamily lower) →
        Name.eval {p | ((projection).projectedFilter H).mem p} N =
          Name.eval {p | H.mem p} tau.val ∩
            Name.eval {p | ((projection).projectedFilter H).mem p} (Name.familySet ⊤ J valid) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
  let valid := (termData n).2 alpha cutOrdinal subset
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation LQ
  have unchanged : ∀ p : SetMembers LQ, upper.encode (inc p) = lower.encode p :=
    (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hs hPacked hT hAlpha carrier rowTop topMem topRows mono
  have hRestricted := M.graphRestriction_mem unions separation hAlpha hPacked
  have hQ : upper.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hLQ : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha hRestricted omega
  have upperOrder : upper.conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed
  have lowerOrder : lower.conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha packed) :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T alpha (graphRestriction alpha packed)
  have hUpperOrder : upper.conditionOrder ∈ M.sets := by
    rw [upperOrder]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hs hPacked omega
  have hLowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [lowerOrder]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha hRestricted omega
  dsimp only
  intro tau f function selected
  refine ⟨M.crossStageMembershipName_mem upper lower inc unchanged pairing unions powers separation
    collection hQ hUpperOrder hLQ (termData n).1 valid tau.val tau.property, ?_⟩
  intro H generic lowerGeneric
  apply M.crossStageMembershipName_eval_of_family upper lower
    ((run).restriction ordinal cutOrdinal subset c.conditionOrder_code)
    ((run).inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hs hPacked hT hAlpha carrier rowTop topMem topRows mono c.conditionOrder_code)
    projection unchanged pairing unions powers separation collection hQ hUpperOrder hLQ hLowerOrder
    (termData n).1 valid tau function ?_ H generic lowerGeneric
  intro sigma A entry
  rw [upperOrder, lowerOrder]
  exact selected sigma A entry

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

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem ordinal trace
local notation "projection" => M.semanticStructuralTrace_completeProjection c a t b d base directed
  T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
  nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
  symmetric1 symmetric2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralPrefixMembershipName_ground (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    let valid := (termData n).2 alpha cutOrdinal subset
    let upper := SetMembers.presentation Q
    let lower := SetMembers.presentation LQ
    ∀ tau : (M.nameDomain upper).names,
      (Name.crossStageMembershipName upper lower inc J valid tau.val).val ∈ M.sets := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
  let valid := (termData n).2 alpha cutOrdinal subset
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation LQ
  have unchanged : ∀ p : SetMembers LQ, upper.encode (inc p) = lower.encode p :=
    (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hs hPacked hT hAlpha carrier rowTop topMem topRows mono
  have hRestricted := M.graphRestriction_mem unions separation hAlpha hPacked
  have hQ : upper.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hLQ : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha hRestricted omega
  have upperOrder : upper.conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed
  have hUpperOrder : upper.conditionOrder ∈ M.sets := by
    rw [upperOrder]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hs hPacked omega
  dsimp only
  intro tau
  exact M.crossStageMembershipName_mem upper lower inc unchanged pairing unions powers separation
    collection hQ hUpperOrder hLQ (termData n).1 valid tau.val tau.property

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

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem ordinal trace
local notation "projection" => M.semanticStructuralTrace_completeProjection c a t b d base directed
  T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
  nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
  symmetric1 symmetric2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralPrefixRefinementEnvironment (degrees : Fin 3 → Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let upper := SetMembers.presentation Q
    let lower := SetMembers.presentation LQ
    let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
    let valid := fun i => (termData (degrees i)).2 alpha cutOrdinal subset
    let validT := (termData 0).2 alpha cutOrdinal subset
    ∀ tau : Fin 3 → (M.nameDomain upper).names,
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation LQ
  let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
  let valid := fun i => (termData (degrees i)).2 alpha cutOrdinal subset
  let validT := (termData 0).2 alpha cutOrdinal subset
  dsimp only
  intro tau
  have ground : ∀ i : Fin 3,
      (Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val).val ∈ M.sets :=
    fun i => M.semanticStructuralPrefixMembershipName_ground c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice (degrees i) (tau i)
  let names : Fin 3 → (M.nameDomain lower).names := fun i =>
    ⟨Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val, ground i⟩
  have hLower : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hFamily := M.familySet_mem lower ⊤ pairing unions powers separation hT
    (M.transitive hLower (lower.encode_mem ⊤)) validT
  refine ⟨![names 0, names 1, names 2, ⟨Name.familySet ⊤ T validT, hFamily⟩], ?_, rfl⟩
  intro i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i

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

noncomputable def semanticStructuralNameLift (tau : Name (SetMembers.presentation LQ)) :
    Name (SetMembers.presentation Q) := Name.rename (SetMembers.presentation Q) inc tau
local notation "liftName" => M.semanticStructuralNameLift c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralNameLift_val (tau : Name (SetMembers.presentation LQ)) :
    (liftName tau).val = tau.val :=
  Name.rename_val_of_encode (s := SetMembers.presentation LQ) (SetMembers.presentation Q) inc
    ((run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hs hPacked hT hAlpha carrier rowTop topMem topRows mono) tau

theorem semanticStructuralNameLift_mem (tau : Name (SetMembers.presentation LQ))
    (ground : tau.val ∈ M.sets) : (liftName tau).val ∈ M.sets := by
  rw [M.semanticStructuralNameLift_val c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice]
  exact ground

theorem semanticStructuralNameLift_eval (H : Set (SetMembers Q))
    (tau : Name (SetMembers.presentation LQ)) :
    Name.eval H (liftName tau) = Name.eval {p | inc p ∈ H} tau :=
  Name.eval_rename (SetMembers.presentation Q) inc H tau

theorem semanticStructuralNameLiftGraph_eq (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName (SetMembers.presentation LQ) z) :
    Name.renameFamilyGraph (SetMembers.presentation Q) inc X valid = identityFunctionGraph X := by
  apply ZFSet.ext
  intro z
  rw [Name.mem_renameFamilyGraph, mem_identityFunctionGraph]
  constructor
  · rintro ⟨tau, member, equal⟩
    have code := M.semanticStructuralNameLift_val c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice tau
    exact ⟨tau.val, member, equal.trans (congrArg (ZFSet.pair tau.val) code)⟩
  · rintro ⟨x, member, rfl⟩
    let tau : Name (SetMembers.presentation LQ) := ⟨x, valid x member⟩
    exact ⟨tau, member,
      (congrArg (ZFSet.pair x) (M.semanticStructuralNameLift_val c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice tau)).symm⟩

theorem semanticStructuralNameLiftGraph_mem (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName (SetMembers.presentation LQ) z) (ground : X ∈ M.sets) :
    Name.renameFamilyGraph (SetMembers.presentation Q) inc X valid ∈ M.sets := by
  rw [M.semanticStructuralNameLiftGraph_eq c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice]
  exact M.identityFunctionGraph_mem pairing unions powers separation ground

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

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem ordinal trace
local notation "projection" => M.semanticStructuralTrace_completeProjection c a t b d base directed
  T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
  nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
  symmetric1 symmetric2 topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralPowerFamily_eval_prefix (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      (run).carriers ordinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers ordinal carrier J
      (by
        obtain ⟨p, rfl⟩ := (c.mem_carrier rowTop).1 topMem
        exact iteratedPairNameFamily_valid p valid1 n)
    let validLower := (termData n).2 alpha cutOrdinal subset
    ∀ H : ConditionFilter (SetMembers Q),
      Name.eval {p | H.mem p} (Name.familySet ⊤ J validUpper) =
        Name.eval {p | ((projection).projectedFilter H).mem p} (Name.familySet ⊤ J validLower) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation LQ
  have unchanged : ∀ p, upper.encode (inc p) = lower.encode p :=
    (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation infinite choice
      hs hPacked hT hAlpha carrier rowTop topMem topRows mono
  have equalTop : upper.encode ⊤ = lower.encode ⊤ := by
    rw [M.refinementHistoryDecodedTop_eq, M.refinementHistoryDecodedTop_eq]
  dsimp only
  intro H
  exact Name.eval_familySet_crossStage upper lower inc unchanged ⊤ ⊤ equalTop _ _ _ {p | H.mem p}

end PartitionPilot.Forcing.TransitiveGround

end OAI
