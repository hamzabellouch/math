import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAlignedLargerCutTests
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementAbsentLiftInsertions

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

theorem semanticStructuralPrefix_refinementSystem :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    RefinementStageSystem M act lower t b d base directed alpha T T2 := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
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
  have hQ : lower.carrier ∈ M.sets := fields 7
  have hOrder : lower.conditionOrder ∈ M.sets := fields 8
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
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨firstValid, firstClosed, firstChildren⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  obtain ⟨secondValid, secondClosed, secondChildren⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T2 valid2 closed2 symmetric2
  exact M.refinementStageSystem act lower t b d base directed pairing unions powers separation collection
    hQ hOrder group nodes nodeOrder maps nodeMaps supports hAlpha hT hT2
    firstValid secondValid firstClosed secondClosed firstChildren secondChildren

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

theorem semanticStructuralSuccessor_insert_absentLift
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable)
    {row A : ZFSet.{u}} (condition : ZFSet.pair row A ∈ upper) :
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
    let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
    let vis := M.stageOneVisibilityName lower valid act b d base directed system.first

    ∀ (meet : L → L → L),
      (∀ (H : ConditionFilter (SetMembers Q)), H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v z : L) (x y : (M.nameDomain lower).names),
          d.principalFix v ≤ (act).stabilizer lower x.val →
          d.principalFix z ≤ (act).stabilizer lower y.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) x.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau.val ∧
            d.principalFix (meet v z) ≤ (act).stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∀ (C E K : L) (U Rf Rc u w : (M.nameDomain lower).names) (F : ZFSet.{u}),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid →
      u.val.val ∈ T → w.val.val ∈ T →
      ∀ pCut q : SetMembers Q,
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → q ≤ pCut →
      Name.ForcesMem q u.val U.val → Name.ForcesMem q w.val U.val →
      (∀ v : L, b.encode v ∈ testedMeetFilter F b.conditionOrder (b.encode E) → K ≤ v) →
      (∀ v : L, E ≤ v → b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) → meet K v = C) →
      M.DecidesVisibilityProfile act lower b d.principalFix T F (cls Rc u).val q →
      Name.ForcesMem q (cls Rf w).val (vis K).val →
      (∀ p, p ≤ q → ¬ Name.ForcesMem p (cls Rf w).val (vis C).val) →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rc u).val (cls Rc v).val) ∧
        ∃ profile, M.DecidesVisibilityProfile act lower b d.principalFix T profile (cls Rf z).val q ∧
          (b.encode C ∉ profile → b.encode K ∉ profile)) →
      ∃ lowerRow lowerA : ZFSet.{u}, lower.encode q = ZFSet.pair lowerRow lowerA ∧
        let spliced := assignmentSplice levels alpha lowerA A
        let inserted := insert (stageOneAssignment idx u.val.val w.val.val) spliced
        ZFSet.pair lowerRow inserted ∈ upper ∧
        ZFSet.pair (ZFSet.pair lowerRow inserted) (ZFSet.pair row A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next ∧
        A ⊆ inserted ∧ stageOneAssignment idx u.val.val w.val.val ∈ inserted ∧
        ZFSet.pair lowerRow (assignmentCut levels alpha inserted) = lower.encode q ∧
        Name.ForcesEq q (cls Rc u).val (cls Rc u).val := by
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
  let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
  let vis := M.stageOneVisibilityName lower valid act b d base directed system.first
  dsimp only
  intro meet descent C E K U Rf Rc u w F idx hu hw pCut q cutCode qp
    activeU activeW capPositive capNegative decisions capVisible nonvisible oldProfiles
  obtain ⟨lowerRow, _, lowerA, _, qCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T alpha lowerPacked (SetMembers.raw_mem q))
  change lower.encode q = ZFSet.pair lowerRow lowerA at qCode
  have alphaNext : alpha ⊆ insert alpha alpha := fun _ h => ZFSet.mem_insert_of_mem _ h
  have nextSubset : insert alpha alpha ⊆ stages := by
    intro x hx
    exact (ZFSet.mem_insert_iff.1 hx).elim (fun e => e ▸ member) (fun h => subset x h)
  have nextOrdinal := ordinalSetProperty_succ cutOrdinal
  let nextRun := (run).restrict nextOrdinal nextSubset
  have nextGround : insert alpha alpha ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have packedNextGround : next ∈ M.sets := M.graphRestriction_mem unions separation nextGround packedGround
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have lowerBelow : ZFSet.pair (ZFSet.pair lowerRow lowerA)
      (ZFSet.pair row (assignmentCut levels alpha A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha next) := by
    rw [graphRestriction_restrict alphaNext]
    change ZFSet.pair (lower.encode q) (lower.encode pCut) ∈ _ at qp
    rwa [qCode, cutCode] at qp
  obtain ⟨spliceCondition, spliceBelow, spliceCut⟩ := nextRun.splice_lifting
    pairing unions powers separation infinite choice nextGround packedNextGround hT hAlpha
    nextOrdinal cutOrdinal alphaNext
    (fun beta fields entry => mono beta fields (pair_mem_graphRestriction.1 entry).1)
    condition lowerBelow
  let spliced := assignmentSplice levels alpha lowerA A
  have exactCut : lower.encode q = ZFSet.pair lowerRow (assignmentCut levels alpha spliced) := by
    rw [spliceCut]
    exact qCode
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have storedNext := pair_mem_graphRestriction.2 ⟨stored, ZFSet.mem_insert alpha alpha⟩
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  let index := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  have indexMem : index ∈ fields 0 := idx
  have oldOrigin (v z : (M.nameDomain lower).names) (hv : v.val.val ∈ T) (hz : z.val.val ∈ T)
      (old : stageOneAssignment index v.val.val z.val.val ∈ spliced) :
      stageOneAssignment index v.val.val z.val.val ∈ A := by
    rcases (mem_assignmentSplice levels alpha lowerA A _).1 old with low | high
    · obtain ⟨_, xi, hxi, edge⟩ := low
      have same := (nextRun.carriers.data.assignment_level_iff storedNext index indexMem
        v.val.val hv z.val.val hz xi).1 edge
      exact False.elim (ZFSet.mem_irrefl alpha (same ▸ hxi))
    · exact high.1
  have same := (run).carriers.stored_successor_eq ordinal member fields stored
  have old := (M.pair_mem_stageTwoConditions c.carrier
    (refinementDataHistoryIndices (insert alpha alpha) next) levels alpha fields lowerRow spliced).1
      (same ▸ spliceCondition)
  have oldTests : stageOneRawTests M fields spliced (lower.encode q) := by
    rw [exactCut]
    exact old.2.2.2.2.2
  have allTests := M.refinementLevelRawTests_insert_absentLift act lower b d alpha
    pairing unions powers separation collection lowerGround lowerOrder nodes hT valid system.indices
    base directed system.first meet descent small C E K U Rf Rc u w F idx q oldTests
    activeU activeW capPositive capNegative decisions capVisible nonvisible
    (fun v z hv hz old => oldProfiles v z hv hz (oldOrigin v z hv hz old))
  have inserted : stageOneAssignment index u.val.val w.val.val ∈
      insert (stageOneAssignment index u.val.val w.val.val) spliced := ZFSet.mem_insert _ _
  rw [exactCut] at allTests
  obtain ⟨insertCondition, insertCut, _⟩ :=
    (run).carriers.stored_successor_insert_extension pairing unions powers separation infinite
      ordinal member fields stored system.indices.index_ground hT c.conditionOrder c.conditionOrder_code
      indexMem hu hw spliceCondition (allTests.1 index indexMem _ hu _ hw inserted)
      (fun v hv z hz old => allTests.2 index indexMem v hv _ hu z hz _ hw
        (ZFSet.mem_insert_of_mem _ old) inserted)
      (fun v hv z hz old => allTests.2 index indexMem _ hu v hv _ hw z hz
        inserted (ZFSet.mem_insert_of_mem _ old))
      (allTests.2 index indexMem _ hu _ hu _ hw _ hw inserted inserted)
  have spliceOrder := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
    (insert alpha alpha) next _ _ _ _).1 spliceBelow
  have retained : A ⊆ insert (stageOneAssignment index u.val.val w.val.val) spliced :=
    fun _ ha => ZFSet.mem_insert_of_mem _ (spliceOrder.2.2.2 ha)
  refine ⟨lowerRow, lowerA, qCode, insertCondition, ?_, retained, inserted, ?_, Name.forcesEq_refl _ _⟩
  · exact (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T
      (insert alpha alpha) next _ _ _ _).2
      ⟨insertCondition, condition, spliceOrder.2.2.1, retained⟩
  · rw [insertCut]
    exact exactCut.symm

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

theorem semanticStructuralSuccessor_insert_visibleLift
    (infinite : Realize M.sets infinity Fin.elim0) (small : M.sets.Countable)
    {row A : ZFSet.{u}} (condition : ZFSet.pair row A ∈ upper) :
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
    let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
    let vis := M.stageOneVisibilityName lower valid act b d base directed system.first
    ∀ (C E : L) (U Rf Rc u w : (M.nameDomain lower).names),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid →
      u.val.val ∈ T → w.val.val ∈ T →
      ∀ pCut : SetMembers Q,
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) →
      Name.ForcesMem pCut u.val U.val → Name.ForcesMem pCut w.val U.val →
      Name.ForcesMem pCut (cls Rf w).val (vis C).val →
      Forces (M.nameDomain lower) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
        ![cls Rf w, cls Rc u, M.stageOneMapName lower pairing unions powers separation collection
          lowerGround lowerOrder hT valid U Rf Rc] pCut →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        ∀ q, q ≤ pCut → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
      ZFSet.pair row (insert (stageOneAssignment idx u.val.val w.val.val) A) ∈ upper ∧
        assignmentCut levels alpha (insert (stageOneAssignment idx u.val.val w.val.val) A) =
          assignmentCut levels alpha A ∧
        ZFSet.pair (ZFSet.pair row (insert (stageOneAssignment idx u.val.val w.val.val) A))
          (ZFSet.pair row A) ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next := by
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
  intro C E U Rf Rc u w idx hu hw pCut cutCode activeU activeW visible mapped fresh
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  let index := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same := (run).carriers.stored_successor_eq ordinal member fields stored
  have old := (M.pair_mem_stageTwoConditions c.carrier
    (refinementDataHistoryIndices (insert alpha alpha) next) levels alpha fields row A).1 (same ▸ condition)
  have oldTests : stageOneRawTests M fields A (lower.encode pCut) := by
    rw [cutCode]
    exact old.2.2.2.2.2
  have allTests := M.refinementLevelRawTests_insert_visibleLift act lower t b d alpha
    pairing unions powers separation collection lowerGround lowerOrder nodes hT valid system.indices
    base directed system.first system.inputs.condition_maps system.inputs.terms_closed small
    C E U Rf Rc u w idx pCut oldTests activeU activeW visible mapped fresh
  have inserted : stageOneAssignment index u.val.val w.val.val ∈
      insert (stageOneAssignment index u.val.val w.val.val) A := ZFSet.mem_insert _ _
  have indexMem : index ∈ fields 0 := idx
  rw [cutCode] at allTests
  exact (run).carriers.stored_successor_insert_extension pairing unions powers separation infinite
    ordinal member fields stored system.indices.index_ground hT c.conditionOrder c.conditionOrder_code
    indexMem hu hw condition (allTests.1 index indexMem _ hu _ hw inserted)
    (fun v hv z hz old => allTests.2 index indexMem v hv _ hu z hz _ hw
      (ZFSet.mem_insert_of_mem _ old) inserted)
    (fun v hv z hz old => allTests.2 index indexMem _ hu v hv _ hw z hz
      inserted (ZFSet.mem_insert_of_mem _ old))
    (allTests.2 index indexMem _ hu _ hu _ hw _ hw inserted inserted)

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

theorem semanticStructuralSuccessor_represented_absentLift
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable)
    {row A : ZFSet.{u}} (condition : ZFSet.pair row A ∈ upper) :
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
    let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
    let vis := M.stageOneVisibilityName lower valid act b d base directed system.first

    ∀ (meet : L → L → L),
      (∀ (H : ConditionFilter (SetMembers Q)), H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v z : L) (x y : (M.nameDomain lower).names),
          d.principalFix v ≤ (act).stabilizer lower x.val →
          d.principalFix z ≤ (act).stabilizer lower y.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) x.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau.val ∧
            d.principalFix (meet v z) ≤ (act).stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∀ (C E K : L) (U Rf Rc u w : (M.nameDomain lower).names) (F : ZFSet.{u}),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid →
      u.val.val ∈ T → w.val.val ∈ T →
      ∀ pCut q : SetMembers Q,
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → q ≤ pCut →
      Name.ForcesMem q u.val U.val → Name.ForcesMem q w.val U.val →
      (∀ v : L, b.encode v ∈ testedMeetFilter F b.conditionOrder (b.encode E) → K ≤ v) →
      (∀ v : L, E ≤ v → b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) → meet K v = C) →
      M.DecidesVisibilityProfile act lower b d.principalFix T F (cls Rc u).val q →
      Name.ForcesMem q (cls Rf w).val (vis K).val →
      (∀ p, p ≤ q → ¬ Name.ForcesMem p (cls Rf w).val (vis C).val) →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rc u).val (cls Rc v).val) ∧
        ∃ profile, M.DecidesVisibilityProfile act lower b d.principalFix T profile (cls Rf z).val q ∧
          (b.encode C ∉ profile → b.encode K ∉ profile)) →
      M.representedDomainConditions lower upper levels alpha T valid idx U Rc u ∈ M.sets ∧
      ∃ lowerRow lowerA : ZFSet.{u}, lower.encode q = ZFSet.pair lowerRow lowerA ∧
        let spliced := assignmentSplice levels alpha lowerA A
        let inserted := insert (stageOneAssignment idx u.val.val w.val.val) spliced
        ZFSet.pair lowerRow inserted ∈ upper ∧
        ZFSet.pair (ZFSet.pair lowerRow inserted) (ZFSet.pair row A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next ∧
        A ⊆ inserted ∧ stageOneAssignment idx u.val.val w.val.val ∈ inserted ∧
        ZFSet.pair lowerRow (assignmentCut levels alpha inserted) = lower.encode q ∧
        Name.ForcesEq q (cls Rc u).val (cls Rc u).val ∧
        ZFSet.pair lowerRow inserted ∈ M.representedDomainConditions lower upper levels alpha T valid
          idx U Rc u := by
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
  let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
  let vis := M.stageOneVisibilityName lower valid act b d base directed system.first
  dsimp only
  intro meet descent C E K U Rf Rc u w F idx hu hw pCut q cutCode qp
    activeU activeW capPositive capNegative decisions capVisible nonvisible oldProfiles
  obtain ⟨lowerRow, lowerA, qCode, insertedCondition, insertedBelow, retained,
      insertedLiteral, exactCut, selfEqual⟩ :=
    M.semanticStructuralSuccessor_insert_absentLift c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice small condition
      meet descent C E K U Rf Rc u w F idx hu hw pCut q cutCode qp
      activeU activeW capPositive capNegative decisions capVisible nonvisible oldProfiles
  have nextGround : insert alpha alpha ∈ M.sets := M.insert_mem pairing unions hAlpha hAlpha
  have packedNextGround : next ∈ M.sets := M.graphRestriction_mem unions separation nextGround packedGround
  have upperGround : upper ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT nextGround packedNextGround omega
  have levelsGround : levels ∈ M.sets :=
    M.refinementDataHistoryLevels_mem pairing unions powers separation nextGround packedNextGround hT
  have indexGround := M.refinementIndexCode_mem pairing hAlpha
    (M.transitive nodes (b.encode_mem C)) (M.transitive nodes (b.encode_mem E))
    U.property Rf.property Rc.property
  refine ⟨M.representedDomainConditions_mem lower pairing unions powers separation collection
    lowerGround lowerOrder upperGround levelsGround hAlpha hT valid indexGround U Rc u,
    lowerRow, lowerA, qCode, insertedCondition, insertedBelow, retained, insertedLiteral,
    exactCut, selfEqual, ?_⟩
  exact (M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerGround lowerOrder upperGround levelsGround hAlpha hT valid indexGround U Rc u lowerRow
    _ q exactCut.symm).2
    ⟨insertedCondition, Or.inr ⟨activeU, u.val, w.val, hu, hw, insertedLiteral, selfEqual⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
