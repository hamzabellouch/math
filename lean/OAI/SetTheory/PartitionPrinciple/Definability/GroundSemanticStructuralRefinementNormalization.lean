import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralFamilyEvaluation
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundSharedRefinementValidity
import OAI.SetTheory.PartitionPrinciple.Transfinite.CrossStageParameterSupports

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
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
include hs hh ordinal trace

variable {alpha : ZFSet.{u}} (hAlpha : alpha ∈ M.sets)
variable (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hAlpha cutOrdinal subset

theorem semanticStructuralPrefixSharedCondition_spec (m : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T m
    ∃ valid : ∀ z ∈ J, IsName lower z,
      J ∈ M.sets ∧ ∀ (n : Nat) (phi : SetFormula n)
        (env : Assignment (M.nameDomain lower) n) (i : Fin n) (K : Subgroup G),
        (d.principalSupportFamily base directed).mem K →
        (∀ j, K ≤ (lowerAct).stabilizer lower (env j).val) →
        (Name.sharedConditionName (M.nameDomain lower) phi env i J valid).val ∈ M.sets ∧
        NiceNameCode lowerAct lower J K
          (Name.sharedConditionName (M.nameDomain lower) phi env i J valid).val ∧
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
          (Name.sharedConditionName (M.nameDomain lower) phi env i J valid) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  have hRestricted := M.graphRestriction_mem unions separation hAlpha hPacked
  have hQ : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha hRestricted omega
  have hOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha hRestricted omega
  have hGraph : (lowerAct).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    have ground := M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh omega
    unfold structuralForcingCarrier at ground
    rw [M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset] at ground
    exact ground
  have maps := M.conditionMapFamily_mem_of_actionGraph lowerAct lower t pairing unions powers separation
    collection hQ group hGraph
  obtain ⟨valid, hJ, terms, children⟩ := M.semanticStructuralPrefixPower_family
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset m
  refine ⟨valid, hJ, ?_⟩
  intro n phi env i K member fixed
  exact M.sharedConditionName_spec lower pairing unions powers separation collection hQ hOrder
    lowerAct t maps phi env i hJ valid terms K fixed
    (d.principalSupportFamily base directed) member children

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

theorem semanticStructuralNameLift_act :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (g : G) (tau : Name (SetMembers.presentation LQ)),
      (upperAct).act (SetMembers.presentation Q) g (liftName tau) =
        liftName ((lowerAct).act (SetMembers.presentation LQ) g tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro g tau
  exact (lowerAct).act_rename_of_equivariant upperAct (SetMembers.presentation LQ)
    (SetMembers.presentation Q) inc
    (fun g p => (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm) g tau

theorem semanticStructuralNameLift_stabilizer :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ tau : Name (SetMembers.presentation LQ),
      (upperAct).stabilizer (SetMembers.presentation Q) (liftName tau) =
        (lowerAct).stabilizer (SetMembers.presentation LQ) tau := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro tau
  apply Subgroup.ext
  intro g
  change (upperAct).act (SetMembers.presentation Q) g (liftName tau) = liftName tau ↔
    (lowerAct).act (SetMembers.presentation LQ) g tau = tau
  rw [M.semanticStructuralNameLift_act c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [M.semanticStructuralNameLift_val c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice] using codes
  · intro equal
    exact congrArg liftName equal

theorem semanticStructuralNameLift_supported :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (K : Subgroup G) (tau : Name (SetMembers.presentation LQ)),
      K ≤ (lowerAct).stabilizer (SetMembers.presentation LQ) tau →
        K ≤ (upperAct).stabilizer (SetMembers.presentation Q) (liftName tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro K tau supported
  rw [M.semanticStructuralNameLift_stabilizer c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice]
  exact supported

theorem semanticStructuralNameLift_hs :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (F : NormalSubgroupFamily G) (tau : Name (SetMembers.presentation LQ)),
      HereditarilySymmetric lowerAct (SetMembers.presentation LQ) F tau →
        HereditarilySymmetric upperAct (SetMembers.presentation Q) F (liftName tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro F tau symmetric
  exact symmetric.rename upperAct (SetMembers.presentation Q) inc
    (fun g p => (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm)

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

theorem semanticStructuralCrossStageName_act :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName (SetMembers.presentation LQ) z),
      (∀ g (sigma : Name (SetMembers.presentation LQ)), sigma.val ∈ J →
        ((lowerAct).act (SetMembers.presentation LQ) g sigma).val ∈ J) →
      ∀ (g : G) (tau : Name (SetMembers.presentation Q)),
        (lowerAct).act (SetMembers.presentation LQ) g
          (Name.crossStageMembershipName (SetMembers.presentation Q)
            (SetMembers.presentation LQ) inc J valid tau) =
        Name.crossStageMembershipName (SetMembers.presentation Q)
          (SetMembers.presentation LQ) inc J valid
          ((upperAct).act (SetMembers.presentation Q) g tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro J valid closed g tau
  exact Name.crossStageMembershipName_act upperAct lowerAct (SetMembers.presentation Q)
    (SetMembers.presentation LQ) inc J valid (fun g p => (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm) closed g tau

theorem semanticStructuralCrossStageName_nice :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName (SetMembers.presentation LQ) z),
      (∀ g (sigma : Name (SetMembers.presentation LQ)), sigma.val ∈ J →
        ((lowerAct).act (SetMembers.presentation LQ) g sigma).val ∈ J) →
      ∀ (K : Subgroup G) (tau : Name (SetMembers.presentation Q)),
        K ≤ (upperAct).stabilizer (SetMembers.presentation Q) tau →
        NiceNameCode lowerAct (SetMembers.presentation LQ) J K
          (Name.crossStageMembershipName (SetMembers.presentation Q)
            (SetMembers.presentation LQ) inc J valid tau).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro J valid closed K tau supported
  exact Name.crossStageMembershipName_nice upperAct lowerAct (SetMembers.presentation Q)
    (SetMembers.presentation LQ) inc J valid (fun g p => (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm) closed K tau supported

theorem semanticStructuralCrossStagePower_hs :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (n : Nat) (K : Subgroup G), (d.principalSupportFamily base directed).mem K →
      ∀ tau : Name (SetMembers.presentation Q),
        K ≤ (upperAct).stabilizer (SetMembers.presentation Q) tau →
        let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
        ∃ valid : ∀ z ∈ J, IsName (SetMembers.presentation LQ) z,
          J ∈ M.sets ∧
          NiceNameCode lowerAct (SetMembers.presentation LQ) J K
            (Name.crossStageMembershipName (SetMembers.presentation Q)
              (SetMembers.presentation LQ) inc J valid tau).val ∧
          HereditarilySymmetric lowerAct (SetMembers.presentation LQ)
            (d.principalSupportFamily base directed)
            (Name.crossStageMembershipName (SetMembers.presentation Q)
              (SetMembers.presentation LQ) inc J valid tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro n K member tau supported
  obtain ⟨valid, ground, closed, children⟩ := M.semanticStructuralPrefixPower_family
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset n
  refine ⟨valid, ground, ?_, ?_⟩
  · exact M.semanticStructuralCrossStageName_nice c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice
      _ valid closed K tau supported
  · exact Name.crossStageMembershipName_hs upperAct lowerAct (SetMembers.presentation Q)
      (SetMembers.presentation LQ) inc _ valid (fun g p => (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm) closed
      (d.principalSupportFamily base directed) K member children tau supported

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

theorem semanticStructuralPrefixRefinementNormalization
    (small : M.sets.Countable) (degrees : Fin 3 → Nat) :
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
        ∀ H : ConditionFilter (SetMembers LQ),
          H.GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode (Name.eval {p | H.mem p} (env 3).val)
            (Name.eval {p | H.mem p} (env 0).val) (Name.eval {p | H.mem p} (env 1).val)
            (Name.eval {p | H.mem p} (env 2).val) →
          ∀ i : Fin 3, Name.eval {p | H.mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (env i.castSucc).val := by
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
  obtain ⟨env, names, last⟩ := M.semanticStructuralPrefixRefinementEnvironment
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice degrees tau
  have hLower : lower.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hJ : ∀ i : Fin 3, J i ∈ M.sets := fun i => (termData (degrees i)).1
  have shape : ∀ i : Fin 3, (env i.castSucc).val.val ⊆ ZFSet.prod (J i) lower.carrier := by
    intro i
    rw [names i]
    exact Name.crossStageMembershipCode_subset upper lower inc (J i) (tau i).val
  let normalized := M.refinementConditionAssignment lower pairing unions powers separation collection
    hLower hOrder J hJ valid env
  have entry : ∀ i : Fin 3, (normalized i.castSucc).val =
      Name.refinementConditionNames (M.nameDomain lower) env J valid i :=
    fun i => M.refinementConditionAssignment_entry lower pairing unions powers separation collection
      hLower hOrder J hJ valid env i
  refine ⟨env, names, last, normalized, entry, rfl, ?_, ?_, ?_⟩
  · exact M.sharedRefinementValidity_top lower pairing unions powers separation collection
      hLower hOrder J hJ valid env small shape
  · intro C member supported
    have closed : ∀ i g (sigma : Name lower), sigma.val ∈ J i →
        ((lowerAct).act lower g sigma).val ∈ J i := by
      intro i
      obtain ⟨_, _, terms, _⟩ := M.semanticStructuralPrefixPower_family
        c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
        rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset (degrees i)
      exact terms
    have closedT : ∀ g (sigma : Name lower), sigma.val ∈ T →
        ((lowerAct).act lower g sigma).val ∈ T := by
      obtain ⟨_, _, terms, _⟩ := M.semanticStructuralPrefixPower_family
        c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
        rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh ordinal trace hAlpha cutOrdinal subset 0
      exact terms
    have fixed := Name.crossStageParameter_support upperAct lowerAct upper lower inc
      (fun g p => (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
        topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm)
      J valid closed (fun i => (tau i).val) (M.nameDomain lower) env names T validT closedT last C supported
    intro i
    obtain ⟨_, _, spec⟩ := M.semanticStructuralPrefixSharedCondition_spec
      c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
      rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
      symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset (degrees i)
    have nice := spec 4 BoundedFormula.refinementValidityFormula.toFormula env i.castSucc C member fixed
    rw [entry i]
    exact nice.2
  · intro H generic oldValid i
    rw [entry i]
    have family : ∀ j, Name.familySet ⊤ (J j) (valid j) ∈ (M.nameDomain lower).names :=
      fun j => M.familySet_mem lower ⊤ pairing unions powers separation (hJ j)
        (M.transitive hLower (lower.encode_mem ⊤)) (valid j)
    exact Name.eval_refinementConditionNames_of_valid (M.nameDomain lower) env J valid
      family H generic shape oldValid i

end PartitionPilot.Forcing.TransitiveGround

end OAI
