import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAssignmentLabelDomainTotality
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAugmentedClassRequests
import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveRefinementMapCoherence

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

theorem semanticStructuralPrefix_representedDomain_ground_downward :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (idx : ZFSet.{u}), idx ∈ M.sets → ∀ (U Rc u : (M.nameDomain lower).names),
    let upper := M.refinementHistoryForcing c.carrier T stages packed
    let D := M.representedDomainConditions lower upper
      (refinementDataHistoryLevels stages packed T) alpha T valid idx U Rc u
    D ∈ M.sets ∧ D ⊆ upper ∧
      ∀ p q, ZFSet.pair q p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed →
        p ∈ D → q ∈ D := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  dsimp only
  intro idx hIdx U Rc u
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
  have hUpper := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hs hPacked hT
  refine ⟨M.representedDomainConditions_mem lower pairing unions powers separation collection
    lowerCarrier lowerOrder hUpper hLevels hAlpha hT valid hIdx U Rc u,
    M.representedDomainConditions_subset lower _ _ _ _ valid idx U Rc u, ?_⟩
  intro p q below represented
  have shapes := ZFSet.pair_mem_prod.1
    ((M.refinementHistoryOrder_partialOrder c.conditionOrder_code T stages packed).relation below)
  obtain ⟨row, _, A, _, rfl⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed shapes.2)
  obtain ⟨newRow, _, newA, _, rfl⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed shapes.1)
  have orderFacts := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    newRow newA row A).1 below
  let pCut : SetMembers Q := SetMembers.ofMem
    (ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A))
    ((run).carriers.cut_mem orderFacts.2.1 member)
  let qCut : SetMembers Q := SetMembers.ofMem
    (ZFSet.pair newRow (assignmentCut (refinementDataHistoryLevels stages packed T) alpha newA))
    ((run).carriers.cut_mem orderFacts.1 member)
  have pCode : lower.encode pCut = ZFSet.pair row
      (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A) := SetMembers.raw_ofMem _ _
  have qCode : lower.encode qCut = ZFSet.pair newRow
      (assignmentCut (refinementDataHistoryLevels stages packed T) alpha newA) := SetMembers.raw_ofMem _ _
  have cutBelow : qCut ≤ pCut := by
    change ZFSet.pair (lower.encode qCut) (lower.encode pCut) ∈ _
    rw [qCode, pCode]
    exact (run).cut_order_le ordinal cutOrdinal subset below
  have branches := (M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerCarrier lowerOrder hUpper hLevels hAlpha hT valid hIdx U Rc u row A pCut pCode).1 represented
  apply (M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerCarrier lowerOrder hUpper hLevels hAlpha hT valid hIdx U Rc u newRow newA qCut qCode).2
  refine ⟨orderFacts.1, ?_⟩
  rcases branches.2 with inactive | ⟨active, v, w, hv, hw, literal, equal⟩
  · exact Or.inl (fun r belowR => inactive r (belowR.trans cutBelow))
  · exact Or.inr ⟨Name.forcesMem_mono active cutBelow, v, w, hv, hw,
      orderFacts.2.2.2 literal, Name.forcesEq_mono equal cutBelow⟩

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

local notation "parentQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "parentLevels" => refinementDataHistoryLevels stages packed T
local notation "gamma" => insert alpha alpha
local notation "nextPacked" => graphRestriction gamma packed
local notation "nextQ" => M.refinementHistoryForcing c.carrier T gamma nextPacked
local notation "nextLevels" => refinementDataHistoryLevels gamma nextPacked T

omit rowAction nodeAction nodeMaps valid2 closed1 closed2 symmetric1 symmetric2 in
theorem semanticStructuralPrefix_representedDomain_of_successor_cut :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (idx : ZFSet.{u}), idx ∈ M.sets → ∀ (U Rc u : (M.nameDomain lower).names),
      ∀ (row A : ZFSet.{u}), ZFSet.pair row A ∈ parentQ →
      ZFSet.pair row (assignmentCut parentLevels gamma A) ∈
        M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u →
      ZFSet.pair row A ∈
        M.representedDomainConditions lower parentQ parentLevels alpha T valid idx U Rc u := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  dsimp only
  intro idx hIdx U Rc u row A condition represented
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hGamma : gamma ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have alphaGamma : alpha ⊆ gamma := fun _ hx => ZFSet.mem_insert_of_mem _ hx
  have gammaSubset : gamma ⊆ stages := by
    intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact member
    · exact subset _ old
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have hNextPacked := M.graphRestriction_mem unions separation hGamma hPacked
  have lowerGround : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hAlpha hLowerPacked omega
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha hLowerPacked omega
  have hParent := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hs hPacked omega
  have hNext := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hGamma hNextPacked omega
  have hParentLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hs hPacked hT
  have hNextLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hGamma hNextPacked hT
  let q : SetMembers Q := SetMembers.ofMem
    (ZFSet.pair row (assignmentCut parentLevels alpha A)) ((run).carriers.cut_mem condition member)
  have cutCode : lower.encode q = ZFSet.pair row (assignmentCut parentLevels alpha A) :=
    SetMembers.raw_ofMem _ _
  have sharedCut : assignmentCut nextLevels alpha (assignmentCut parentLevels gamma A) =
      assignmentCut parentLevels alpha A := by
    rw [(run).carriers.data.prefix_cut gammaSubset alphaGamma, assignmentCut_nested alphaGamma]
  have nextCutCode : lower.encode q =
      ZFSet.pair row (assignmentCut nextLevels alpha (assignmentCut parentLevels gamma A)) := by
    rw [sharedCut]
    exact cutCode
  have branches := (M.pair_mem_representedDomainConditions lower
    pairing unions powers separation collection lowerGround lowerOrder hNext hNextLevels hAlpha hT
    valid hIdx U Rc u row (assignmentCut parentLevels gamma A) q nextCutCode).1 represented
  apply (M.pair_mem_representedDomainConditions lower
    pairing unions powers separation collection lowerGround lowerOrder hParent hParentLevels hAlpha hT
    valid hIdx U Rc u row A q cutCode).2
  refine ⟨condition, ?_⟩
  rcases branches.2 with inactive | ⟨active, v, w, hv, hw, literal, equal⟩
  · exact Or.inl inactive
  · exact Or.inr ⟨active, v, w, hv, hw,
      assignmentCut_subset parentLevels gamma A literal, equal⟩

variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)

include infinite choice in
theorem semanticStructuralPrefix_representedDomain_persistent_dense :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma nextPacked
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid →
      (∀ u : (M.nameDomain lower).names, u.val.val ∈ T →
        M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u ∈ M.sets ∧
        Dense {p : SetMembers nextQ | SetMembers.raw p ∈
          M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u}) →
      ∀ u : (M.nameDomain lower).names, u.val.val ∈ T →
        M.representedDomainConditions lower parentQ parentLevels alpha T valid idx U Rc u ∈ M.sets ∧
        Dense {p : SetMembers parentQ | SetMembers.raw p ∈
          M.representedDomainConditions lower parentQ parentLevels alpha T valid idx U Rc u} := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T gamma nextPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have hGamma : gamma ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have gammaOrdinal : ordinalSetProperty gamma := ordinalSetProperty_succ cutOrdinal
  have gammaSubset : gamma ⊆ stages := by
    intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact member
    · exact subset _ old
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  let restriction := (run).restriction ordinal gammaOrdinal gammaSubset c.conditionOrder_code
  let inclusion := (run).inclusion ordinal gammaOrdinal gammaSubset pairing unions powers separation
    infinite choice hs hPacked hT hGamma carrier rowTop topMem topRows mono c.conditionOrder_code
  have projection : CompleteProjection restriction inclusion :=
    M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace gamma hGamma gammaOrdinal gammaSubset infinite choice
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  dsimp only
  intro C E U Rf Rc index successorDensity u hu
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  have hIdx : idx ∈ M.sets := M.transitive system.indices.index_ground index
  have groundDownward := M.semanticStructuralPrefix_representedDomain_ground_downward
    c a t b d base directed T T2 rowTop pairing unions powers separation collection
    carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
    idx hIdx U Rc u
  refine ⟨groundDownward.1, ?_⟩
  intro p
  obtain ⟨q, qp, represented⟩ := projection.dense_preimage (successorDensity u hu).2 p
  obtain ⟨row, _rowMem, A, _dataMem, qCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed (SetMembers.raw_mem q))
  have parentMember : ZFSet.pair row A ∈ parentQ := qCode ▸ SetMembers.raw_mem q
  have nextCode : SetMembers.raw (restriction q) =
      ZFSet.pair row (assignmentCut parentLevels gamma A) :=
    (run).restrictionFunction_raw ordinal gammaOrdinal gammaSubset q row A qCode
  have representedCut : ZFSet.pair row (assignmentCut parentLevels gamma A) ∈
      M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u := by
    change SetMembers.raw (restriction q) ∈
      M.representedDomainConditions lower nextQ nextLevels alpha T valid idx U Rc u at represented
    exact nextCode ▸ represented
  refine ⟨q, qp, ?_⟩
  change SetMembers.raw q ∈
    M.representedDomainConditions lower parentQ parentLevels alpha T valid idx U Rc u
  rw [qCode]
  exact M.semanticStructuralPrefix_representedDomain_of_successor_cut
    c a t b d T T2 rowTop pairing unions powers separation collection
    carrier rowOrderGround group nodes nodeOrder supports hT hT2 omega valid1
    topMem topRows hs hh ordinal trace member idx hIdx U Rc u row A parentMember representedCut

end PartitionPilot.Forcing.TransitiveGround

end OAI
