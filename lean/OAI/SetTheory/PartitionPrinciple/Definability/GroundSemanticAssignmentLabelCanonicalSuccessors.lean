import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAssignmentLabelDomainTotality
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticRepresentedDomainEasyCases
import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveRefinementInclusionCoherence

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
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

local notation "next" => graphRestriction (insert alpha alpha) packed
local notation "upper" => M.refinementHistoryForcing c.carrier T (insert alpha alpha) next
local notation "levels" => refinementDataHistoryLevels (insert alpha alpha) next T
local notation "packedGround" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "lowerGround" => M.refinementHistoryForcing_mem pairing unions powers separation
  carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega
local notation "orderGround" => M.refinementHistoryOrder_mem pairing unions powers separation
  carrier rowOrderGround hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega

theorem semanticStructuralPrefix_assignment_tests :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
    let lowerOrder : lower.conditionOrder ∈ M.sets := by
      rw [M.refinementHistoryDecodedOrder_eq]
      exact orderGround
    ∀ (p : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)) (row A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair row A →
      M.refinementLevelTests lower pairing unions powers separation collection lowerGround lowerOrder hT valid
        act b d base directed system.first alpha T2 A
        ((run).restriction ordinal cutOrdinal subset c.conditionOrder_code p) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact orderGround
  dsimp only
  intro p row A code
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have source : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed :=
    code ▸ SetMembers.raw_mem p
  have original := ((M.mem_refinementHistoryForcing c.carrier T stages packed _).1 source).2
  have tested := (forcingHistoryConditionCode_lookup_iff (run).carriers.data.function).1 original
    alpha member (refinementFormulaDataCode fields) stored
  have raw := (stageTwoConditionCode_pair_iff M fields _ alpha row A).1
    ((packedSuccessorConditionCode_code_iff M _ alpha fields _).1 tested)
  have rawTests : stageOneRawTests M fields A
      (lower.encode ((run).restriction ordinal cutOrdinal subset c.conditionOrder_code p)) := by
    change stageOneRawTests M fields A
      (SetMembers.raw ((run).restrictionFunction ordinal cutOrdinal subset p))
    rw [(run).restrictionFunction_raw ordinal cutOrdinal subset p row A code]
    exact raw.2
  exact (M.refinementLevelRawTests_iff act lower b d alpha pairing unions powers separation collection
    lowerGround lowerOrder nodes hT valid system.indices base directed system.first A
    ((run).restriction ordinal cutOrdinal subset c.conditionOrder_code p)).1 rawTests

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
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
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
include hs hh ordinal trace member
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

theorem semanticStructuralAssignmentLabel_subset_quotients :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      (run).carriers ordinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let upper := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices lowerAct lower b d alpha T T2 valid →
      ∀ (H : ConditionFilter (SetMembers Q)),
      let label := Name.refinementAssignmentLabel upper inc ⊤ T valid
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) Rf Rc
      Name.eval {p | H.mem p} label ⊆ ZFSet.prod
        (Name.eval {q | H.mem (inc q)} (Name.refinementQuotient T valid U.val Rc.val))
        (Name.eval {q | H.mem (inc q)} (Name.refinementQuotient T valid U.val Rf.val)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  let upper := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice
  dsimp only
  intro C E U Rf Rc index H z memberLabel
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  obtain ⟨p, v, w, hp, hv, hw, ⟨row, A, code, entry⟩, equal⟩ :=
    (Name.mem_eval_refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val
      {p | H.mem p} H.top_mem z).1 memberLabel
  let gv : (M.nameDomain lower).names := ⟨v, M.transitive hT hv⟩
  let gw : (M.nameDomain lower).names := ⟨w, M.transitive hT hw⟩
  have tests := M.semanticStructuralPrefix_assignment_tests c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member p row A code
  have active := ((tests C E U Rf Rc index).1 gv gw hv hw entry).1
  have projectedMember : (projection.projectedFilter H).mem
      ((run).restriction ordinal cutOrdinal subset c.conditionOrder_code p) :=
    (projection.projectedFilter_mem_iff H _).2 ⟨p, hp, rfl⟩
  rw [← equal]
  apply ZFSet.pair_mem_prod.2
  constructor
  · exact (Name.mem_eval _ _ _).2 ⟨_,
      (run).restriction ordinal cutOrdinal subset c.conditionOrder_code p,
      (Name.entry_refinementQuotient T valid U.val Rc.val _ _).2 ⟨v, hv, active.1, rfl⟩,
      projectedMember, rfl⟩
  · exact (Name.mem_eval _ _ _).2 ⟨_,
      (run).restriction ordinal cutOrdinal subset c.conditionOrder_code p,
      (Name.entry_refinementQuotient T valid U.val Rf.val _ _).2 ⟨w, hw, active.2, rfl⟩,
      projectedMember, rfl⟩

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
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
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
include hs hh ordinal trace member
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

local notation "gamma" => insert alpha alpha
local notation "hGamma" => M.insert_mem pairing unions hAlpha hAlpha
local notation "gammaOrdinal" => ordinalSetProperty_succ cutOrdinal
local notation "alphaGamma" => (fun (x : ZFSet) (hx : x ∈ alpha) => ZFSet.mem_insert_of_mem alpha hx)
local notation "gammaSubset" => (fun (x : ZFSet) (hx : x ∈ gamma) =>
  Or.elim (Iff.mp ZFSet.mem_insert_iff hx) (fun equal => Eq.mpr (congrArg (fun z => z ∈ stages) equal) member)
    (fun old => subset x old))
local notation "gammaPacked" => graphRestriction gamma packed
local notation "gammaPackedGround" => M.graphRestriction_mem unions separation hGamma hPacked
local notation "gammaRun" => RecursiveRefinementOrderHistory.restrict run gammaOrdinal gammaSubset
local notation "GQ" => M.refinementHistoryForcing c.carrier T gamma gammaPacked
local notation "nestedLQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha gammaPacked)
local notation "gammaMono" => (fun level fields entry => mono level fields
  (And.left (Iff.mp pair_mem_graphRestriction entry)))
local notation "successorInclude" => RecursiveRefinementOrderHistory.inclusionFunction run ordinal gammaOrdinal gammaSubset
  pairing unions powers separation infinite choice hs hPacked hT hGamma carrier rowTop topMem topRows mono
local notation "nestedInclude" => RecursiveRefinementOrderHistory.inclusionFunction gammaRun gammaOrdinal cutOrdinal alphaGamma
  pairing unions powers separation infinite choice hGamma gammaPackedGround hT hAlpha carrier
  rowTop topMem topRows gammaMono
local notation "toNested" => (fun x : SetMembers LQ => SetMembers.ofMem (SetMembers.raw x)
  (Eq.mpr (congrArg (fun h => SetMembers.raw x ∈ M.refinementHistoryForcing c.carrier T alpha h)
    (graphRestriction_restrict alphaGamma)) (SetMembers.raw_mem x)))
local notation "prefixInclude" => (fun x : SetMembers LQ => nestedInclude (toNested x))

theorem semanticStructuralAssignmentLabel_eval_successor_lift :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      (run).carriers ordinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma gammaPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T gamma gammaPacked
      (gammaRun).carriers gammaOrdinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let middle := SetMembers.presentation GQ
    let upper := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices lowerAct lower b d alpha T T2 valid →
      ∀ (H : ConditionFilter (SetMembers Q)),
      Name.eval {p | H.mem p} (Name.refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val) =
        Name.eval {p | H.mem p} (Name.rename upper successorInclude
          (Name.refinementAssignmentLabel middle prefixInclude ⊤ T valid idx Rf.val Rc.val)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma gammaPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T gamma gammaPacked
    (gammaRun).carriers gammaOrdinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  let middle := SetMembers.presentation GQ
  let upper := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace gamma hGamma gammaOrdinal gammaSubset infinite choice
  have successorCode (p : SetMembers GQ) : SetMembers.raw (successorInclude p) = SetMembers.raw p :=
    (run).inclusionFunction_raw ordinal gammaOrdinal gammaSubset pairing unions powers separation
      infinite choice hs hPacked hT hGamma carrier rowTop topMem topRows mono p
  have prefixCode (p : SetMembers LQ) : SetMembers.raw (prefixInclude p) = SetMembers.raw p :=
    ((gammaRun).inclusionFunction_raw gammaOrdinal cutOrdinal alphaGamma pairing unions powers separation
      infinite choice hGamma gammaPackedGround hT hAlpha carrier rowTop topMem topRows gammaMono (toNested p)).trans
      (SetMembers.raw_ofMem _ _)
  have directCode (p : SetMembers LQ) : SetMembers.raw (inc p) = SetMembers.raw p :=
    (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation
      infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono p
  have compose (p : SetMembers LQ) : successorInclude (prefixInclude p) = inc p := by
    apply SetMembers.raw_injective Q
    rw [successorCode, prefixCode, directCode]
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  let fields := M.refinementLevelFormulaData lowerAct lower b d alpha T T2 valid
  dsimp only
  intro C E U Rf Rc index H
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  have atLevel (v w : Name lower) (hv : v.val ∈ T) (hw : w.val ∈ T) :
      ZFSet.pair (stageOneAssignment idx v.val w.val) alpha ∈ levels :=
    (run).carriers.data.coverage alpha member fields stored idx index v.val hv w.val hw
  rw [Name.eval_rename]
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, v, w, hp, hv, hw, ⟨row, A, code, literal⟩, equal⟩ :=
      (Name.mem_eval_refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val
        {p | H.mem p} H.top_mem z).1 hz
    let q := (run).restriction ordinal gammaOrdinal gammaSubset c.conditionOrder_code p
    have hq : (projection.projectedFilter H).mem q :=
      (projection.projectedFilter_mem_iff H q).2 ⟨p, hp, rfl⟩
    have cutCode : middle.encode q = ZFSet.pair row (assignmentCut levels gamma A) :=
      (run).restrictionFunction_raw ordinal gammaOrdinal gammaSubset p row A code
    have cutLiteral : stageOneAssignment idx v.val w.val ∈ assignmentCut levels gamma A :=
      (mem_assignmentCut levels gamma A _).2 ⟨literal, alpha, ZFSet.mem_insert alpha alpha, atLevel v w hv hw⟩
    refine (Name.mem_eval_refinementAssignmentLabel middle prefixInclude ⊤ T valid idx Rf.val Rc.val
      {q | H.mem (successorInclude q)} (projection.projectedFilter H).top_mem z).2
      ⟨q, v, w, hq, hv, hw, ⟨row, assignmentCut levels gamma A, cutCode, cutLiteral⟩, ?_⟩
    simpa only [Set.mem_ofPred_eq, compose] using equal
  · intro hz
    obtain ⟨q, v, w, hq, hv, hw, ⟨row, A, code, literal⟩, equal⟩ :=
      (Name.mem_eval_refinementAssignmentLabel middle prefixInclude ⊤ T valid idx Rf.val Rc.val
        {q | H.mem (successorInclude q)} (projection.projectedFilter H).top_mem z).1 hz
    have parentCode : upper.encode (successorInclude q) = ZFSet.pair row A :=
      (successorCode q).trans code
    refine (Name.mem_eval_refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val
      {p | H.mem p} H.top_mem z).2
      ⟨successorInclude q, v, w, hq, hv, hw, ⟨row, A, parentCode, literal⟩, ?_⟩
    simpa only [Set.mem_ofPred_eq, compose] using equal

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
private theorem assignmentLabel_raw_congr
    (P1 P2 Q1 Q2 : ZFSet.{u}) (lowerEq : P1 = P2) (upperEq : Q1 = Q2)
    (order1 : PartialOrder (SetMembers P1)) (order2 : PartialOrder (SetMembers P2))
    (orderEq : HEq order1 order2)
    (top1 : @OrderTop (SetMembers P1) order1.toLE)
    (top2 : @OrderTop (SetMembers P2) order2.toLE)
    (f1 : SetMembers P1 → SetMembers Q1) (f2 : SetMembers P2 → SetMembers Q2)
    (codes1 : ∀ p, SetMembers.raw (f1 p) = SetMembers.raw p)
    (codes2 : ∀ p, SetMembers.raw (f2 p) = SetMembers.raw p)
    (one1 : SetMembers Q1) (one2 : SetMembers Q2)
    (oneEq : SetMembers.raw one1 = SetMembers.raw one2)
    (T idx : ZFSet.{u})
    (valid1 : ∀ z ∈ T, IsName (SetMembers.presentation P1) z)
    (valid2 : ∀ z ∈ T, IsName (SetMembers.presentation P2) z)
    (Rf1 Rc1 : Name (SetMembers.presentation P1))
    (Rf2 Rc2 : Name (SetMembers.presentation P2))
    (fineEq : Rf1.val = Rf2.val) (coarseEq : Rc1.val = Rc2.val) :
    (show Name (SetMembers.presentation Q1) from
     letI := order1; letI := top1
     Name.refinementAssignmentLabel (SetMembers.presentation Q1) f1 one1 T valid1 idx Rf1 Rc1).val =
    (show Name (SetMembers.presentation Q2) from
     letI := order2; letI := top2
     Name.refinementAssignmentLabel (SetMembers.presentation Q2) f2 one2 T valid2 idx Rf2 Rc2).val := by
  subst P2
  subst Q2
  cases orderEq
  have tops : top1 = top2 := Subsingleton.elim _ _
  subst top2
  have maps : f1 = f2 := funext fun p =>
    SetMembers.raw_injective Q1 ((codes1 p).trans (codes2 p).symm)
  subst f2
  have ones : one1 = one2 := SetMembers.raw_injective Q1 oneEq
  subst one2
  have fine : Rf1 = Rf2 := Subtype.ext fineEq
  have coarse : Rc1 = Rc2 := Subtype.ext coarseEq
  subst Rf2
  subst Rc2
  rfl

private theorem decoded_order_heq
    (M : TransitiveGround.{u}) {R : Type u} [PartialOrder R] (c : Presentation R)
    (T alpha h1 h2 : ZFSet.{u}) (equal : h1 = h2) :
    HEq (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha h1)
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha h2) := by
  subst h2
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
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "levels" => refinementDataHistoryLevels stages packed T
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "pi" => RecursiveRefinementOrderHistory.restrictionFunction run ordinal cutOrdinal subset
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace member
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

local notation "gamma" => insert alpha alpha
local notation "hGamma" => M.insert_mem pairing unions hAlpha hAlpha
local notation "gammaOrdinal" => ordinalSetProperty_succ cutOrdinal
local notation "alphaGamma" => (fun (x : ZFSet) (hx : x ∈ alpha) => ZFSet.mem_insert_of_mem alpha hx)
local notation "gammaSubset" => (fun (x : ZFSet) (hx : x ∈ gamma) =>
  Or.elim (Iff.mp ZFSet.mem_insert_iff hx) (fun equal => Eq.mpr (congrArg (fun z => z ∈ stages) equal) member)
    (fun old => subset x old))
local notation "gammaPacked" => graphRestriction gamma packed
local notation "gammaPackedGround" => M.graphRestriction_mem unions separation hGamma hPacked
local notation "gammaRun" => RecursiveRefinementOrderHistory.restrict run gammaOrdinal gammaSubset
local notation "GQ" => M.refinementHistoryForcing c.carrier T gamma gammaPacked
local notation "nestedLQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha gammaPacked)
local notation "gammaMono" => (fun level fields entry => mono level fields
  (And.left (Iff.mp pair_mem_graphRestriction entry)))
local notation "successorInclude" => RecursiveRefinementOrderHistory.inclusionFunction run ordinal gammaOrdinal gammaSubset
  pairing unions powers separation infinite choice hs hPacked hT hGamma carrier rowTop topMem topRows mono
local notation "nestedInclude" => RecursiveRefinementOrderHistory.inclusionFunction gammaRun gammaOrdinal cutOrdinal alphaGamma
  pairing unions powers separation infinite choice hGamma gammaPackedGround hT hAlpha carrier
  rowTop topMem topRows gammaMono
local notation "toNested" => (fun x : SetMembers LQ => SetMembers.ofMem (SetMembers.raw x)
  (Eq.mpr (congrArg (fun h => SetMembers.raw x ∈ M.refinementHistoryForcing c.carrier T alpha h)
    (graphRestriction_restrict alphaGamma)) (SetMembers.raw_mem x)))
local notation "prefixInclude" => (fun x : SetMembers LQ => nestedInclude (toNested x))

local notation "gammaHistory" => graphRestriction gamma history
local notation "gammaHistoryGround" => M.graphRestriction_mem unions separation hGamma hh
local notation "gammaTrace" => OrdinalRecursionTrace.restrict trace gammaOrdinal gammaSubset
local notation "canonicalPacked" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 gamma gammaHistory
local notation "canonicalRun" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 gammaOrdinal gammaTrace
local notation "CQ" => M.refinementHistoryForcing c.carrier T gamma canonicalPacked
local notation "CLQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha canonicalPacked)
local notation "canonicalAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hGamma gammaHistoryGround gammaOrdinal gammaTrace
local notation "canonicalLowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows gammaHistoryGround gammaTrace hAlpha cutOrdinal alphaGamma
local notation "middleAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hGamma gammaOrdinal gammaSubset
local notation "canonicalWitnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hGamma gammaHistoryGround gammaOrdinal gammaTrace
local notation "canonicalMono" => M.structuralHistory_rawTests_mono t b d base directed T T2 gamma gammaHistory
  pairing unions powers separation collection group nodes supports gammaHistoryGround hT canonicalWitnesses
local notation "canonicalGround" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, gamma, gammaHistory]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hGamma (Fin.cases gammaHistoryGround (fun j => Fin.elim0 j)))))))))
local notation "canonicalInclude" => RecursiveRefinementOrderHistory.inclusionFunction canonicalRun gammaOrdinal cutOrdinal alphaGamma
  pairing unions powers separation infinite choice hGamma canonicalGround hT hAlpha carrier rowTop topMem topRows canonicalMono
local notation "middleLift" => M.semanticStructuralNameLift c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hGamma gammaOrdinal gammaSubset infinite choice

theorem semanticStructuralAssignmentLabel_canonical_successor_name :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      (run).carriers ordinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma gammaPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T gamma gammaPacked
      (gammaRun).carriers gammaOrdinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation LQ
    let middle := SetMembers.presentation GQ
    let upper := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma canonicalPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T gamma canonicalPacked
      (canonicalRun).carriers gammaOrdinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha canonicalPacked)
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha canonicalPacked)
      ((canonicalRun).carriers.restrict cutOrdinal alphaGamma) cutOrdinal carrier rowTop topMem topRows
    let canonicalLower := SetMembers.presentation CLQ
    let canonicalUpper := SetMembers.presentation CQ
    let canonicalValid := M.refinementHistoryRowNameFamily_valid c ((canonicalRun).carriers.restrict cutOrdinal alphaGamma)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices lowerAct lower b d alpha T T2 valid →
      ∃ (Uc Rfc Rcc : (M.nameDomain canonicalLower).names),
        Uc.val.val = U.val.val ∧ Rfc.val.val = Rf.val.val ∧ Rcc.val.val = Rc.val.val ∧
        idx ∈ M.niceRefinementIndices canonicalLowerAct canonicalLower b d alpha T T2 canonicalValid ∧
        let canonicalLabel := Name.refinementAssignmentLabel canonicalUpper canonicalInclude ⊤ T
          canonicalValid idx Rfc.val Rcc.val
        let prefixLabel := Name.refinementAssignmentLabel middle prefixInclude ⊤ T valid idx Rf.val Rc.val
        canonicalLabel.val = prefixLabel.val ∧ canonicalLabel.val ∈ M.sets ∧
        d.principalFix E ≤ (canonicalAct).stabilizer canonicalUpper canonicalLabel ∧
        HereditarilySymmetric canonicalAct canonicalUpper (d.principalSupportFamily base directed) canonicalLabel ∧
        prefixLabel.val ∈ M.sets ∧ d.principalFix E ≤ (middleAct).stabilizer middle prefixLabel ∧
        HereditarilySymmetric middleAct middle (d.principalSupportFamily base directed) prefixLabel ∧
        (middleLift prefixLabel).val = canonicalLabel.val ∧
        (middleLift prefixLabel).val ∈ M.sets ∧
        d.principalFix E ≤ (upperAct).stabilizer upper (middleLift prefixLabel) ∧
        HereditarilySymmetric upperAct upper (d.principalSupportFamily base directed) (middleLift prefixLabel) ∧
        ∀ H : ConditionFilter (SetMembers Q),
          Name.eval {p | H.mem p} (Name.refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val) =
            Name.eval {p | H.mem p} (middleLift prefixLabel) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma gammaPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T gamma gammaPacked
    (gammaRun).carriers gammaOrdinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation LQ
  let middle := SetMembers.presentation GQ
  let upper := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma canonicalPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T gamma canonicalPacked
    (canonicalRun).carriers gammaOrdinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha canonicalPacked)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha canonicalPacked)
    ((canonicalRun).carriers.restrict cutOrdinal alphaGamma) cutOrdinal carrier rowTop topMem topRows
  let canonicalLower := SetMembers.presentation CLQ
  let canonicalUpper := SetMembers.presentation CQ
  let canonicalValid := M.refinementHistoryRowNameFamily_valid c ((canonicalRun).carriers.restrict cutOrdinal alphaGamma)
    cutOrdinal carrier T valid1
  dsimp only
  intro C E U Rf Rc index
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let IndexProperty := fun (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet))
      (act : @PosetAction G _ (SetMembers domainSet) order) =>
    letI := order
    ∀ top : OrderTop (SetMembers domainSet),
      letI := top
      ∀ familyValid : ∀ z ∈ T, IsName (SetMembers.presentation domainSet) z,
        ∃ (U1 Rf1 Rc1 : (M.nameDomain (SetMembers.presentation domainSet)).names),
          U1.val.val = U.val.val ∧ Rf1.val.val = Rf.val.val ∧ Rc1.val.val = Rc.val.val ∧
          idx ∈ M.niceRefinementIndices act (SetMembers.presentation domainSet) b d alpha T T2 familyValid
  have originalIndex : IndexProperty LQ
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)) lowerAct := by
    intro top familyValid
    have topEq : top = M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows := Subsingleton.elim _ _
    subst top
    exact ⟨U, Rf, Rc, rfl, rfl, rfl, index⟩
  have canonicalIndex := (M.semanticStructuralPrefixAction_subhistory_property c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset hGamma gammaOrdinal alphaGamma gammaSubset IndexProperty).2 originalIndex
  obtain ⟨Uc, Rfc, Rcc, uEq, fineEq, coarseEq, indexC⟩ := canonicalIndex inferInstance canonicalValid
  have idxEq : refinementIndexCode alpha (b.encode C) (b.encode E) Uc.val.val Rfc.val.val Rcc.val.val = idx := by
    rw [uEq, fineEq, coarseEq]
  have canonicalGood := M.semanticStructuralAssignmentLabel_ground_supported_hs c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hGamma gammaHistoryGround gammaOrdinal gammaTrace (ZFSet.mem_insert alpha alpha)
    infinite choice C E Uc Rfc Rcc (idxEq.symm ▸ indexC)
  let canonicalLabel := Name.refinementAssignmentLabel canonicalUpper canonicalInclude ⊤ T canonicalValid idx Rfc.val Rcc.val
  let prefixLabel := Name.refinementAssignmentLabel middle prefixInclude ⊤ T valid idx Rf.val Rc.val
  have canonicalGood' : canonicalLabel.val ∈ M.sets ∧
      d.principalFix E ≤ (canonicalAct).stabilizer canonicalUpper canonicalLabel ∧
      HereditarilySymmetric canonicalAct canonicalUpper (d.principalSupportFamily base directed) canonicalLabel := by
    simpa only [idxEq] using canonicalGood
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 gamma history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 gammaSubset)
  have nestedEq := (congrArg (graphRestriction alpha) packedEq).trans (graphRestriction_restrict alphaGamma)
  have labelEq : canonicalLabel.val = prefixLabel.val := by
    apply assignmentLabel_raw_congr CLQ LQ CQ GQ
      (congrArg (M.refinementHistoryForcing c.carrier T alpha) nestedEq)
      (congrArg (M.refinementHistoryForcing c.carrier T gamma) packedEq)
      _ _ (decoded_order_heq M c T alpha _ _ nestedEq) _ _ canonicalInclude prefixInclude
    · exact (canonicalRun).inclusionFunction_raw gammaOrdinal cutOrdinal alphaGamma pairing unions powers separation
        infinite choice hGamma canonicalGround hT hAlpha carrier rowTop topMem topRows canonicalMono
    · intro p
      exact ((gammaRun).inclusionFunction_raw gammaOrdinal cutOrdinal alphaGamma pairing unions powers separation
        infinite choice hGamma gammaPackedGround hT hAlpha carrier rowTop topMem topRows gammaMono (toNested p)).trans
          (SetMembers.raw_ofMem _ _)
    · exact (M.refinementHistoryDecodedTop_eq c.conditionOrder_code T gamma canonicalPacked
        (canonicalRun).carriers gammaOrdinal carrier rowTop topMem topRows).trans
        (M.refinementHistoryDecodedTop_eq c.conditionOrder_code T gamma gammaPacked
          (gammaRun).carriers gammaOrdinal carrier rowTop topMem topRows).symm
    · exact fineEq
    · exact coarseEq
  let LabelProperty := fun (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet))
      (act : @PosetAction G _ (SetMembers domainSet) order) =>
    ∃ tau : Name (SetMembers.presentation domainSet), tau.val = prefixLabel.val ∧ tau.val ∈ M.sets ∧
      act.stabilizer (SetMembers.presentation domainSet) tau ≥ d.principalFix E ∧
      HereditarilySymmetric act (SetMembers.presentation domainSet) (d.principalSupportFamily base directed) tau
  have canonicalProperty : LabelProperty CQ
      (M.refinementHistoryPartialOrder c.conditionOrder_code T gamma canonicalPacked) canonicalAct :=
    ⟨canonicalLabel, labelEq, canonicalGood'⟩
  have prefixProperty := (M.semanticStructuralPrefixAction_restricted_property c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hGamma gammaOrdinal gammaSubset LabelProperty).1 canonicalProperty
  obtain ⟨tau, tauEq, ground, supported, hsName⟩ := prefixProperty
  have tauSame : tau = prefixLabel := Subtype.ext tauEq
  subst tau
  refine ⟨Uc, Rfc, Rcc, uEq, fineEq, coarseEq, indexC, labelEq,
    canonicalGood'.1, canonicalGood'.2.1, canonicalGood'.2.2, ground, supported, hsName, ?_, ?_, ?_, ?_, ?_⟩
  · exact (M.semanticStructuralNameLift_val c a t b d base directed T T2 rowTop pairing unions powers separation
      collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega
      valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hGamma gammaOrdinal
      gammaSubset infinite choice prefixLabel).trans labelEq.symm
  · exact M.semanticStructuralNameLift_mem c a t b d base directed T T2 rowTop pairing unions powers separation
      collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega
      valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hGamma gammaOrdinal
      gammaSubset infinite choice prefixLabel ground
  · exact M.semanticStructuralNameLift_supported c a t b d base directed T T2 rowTop pairing unions powers separation
      collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega
      valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hGamma gammaOrdinal
      gammaSubset infinite choice (d.principalFix E) prefixLabel supported
  · exact M.semanticStructuralNameLift_hs c a t b d base directed T T2 rowTop pairing unions powers separation
      collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega
      valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hGamma gammaOrdinal
      gammaSubset infinite choice (d.principalSupportFamily base directed) prefixLabel hsName
  · exact M.semanticStructuralAssignmentLabel_eval_successor_lift c a t b d base directed T T2 rowTop pairing
      unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps
      supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
      member infinite choice C E U Rf Rc index

end PartitionPilot.Forcing.TransitiveGround

end OAI
