import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticRepresentedDomainAbsentLift
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFixedIndexAssignmentSlices
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundStoredVisitCertificates

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

theorem semanticStructuralPrefix_assignmentClassRequests
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let I := M.niceRefinementIndices act lower b d alpha T T2 valid
    let selected := assignmentOnIndices I T A
    let graphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid selected
    let bound := M.groundRelations T lower.carrier
    let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
    selected ∈ M.sets ∧ M.groundEmbeddable selected ZFSet.omega ∧
    (∀ side, graphs side ∈ M.sets ∧ ZFSet.IsFunc selected bound (graphs side)) ∧
    J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
    (∀ z ∈ J, IsName lower z) ∧
    (∀ z : Name lower, z.val ∈ J →
      HereditarilySymmetric act lower (d.principalSupportFamily base directed) z ∧
      ∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
    (∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names)
      (_idx : refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ I)
      (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∀ (side : Fin 2) y, ZFSet.pair (stageOneAssignment
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val w.val) y ∈ graphs side ↔
        y = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let I := M.niceRefinementIndices act lower b d alpha T T2 valid
  let selected := assignmentOnIndices I T A
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
  have candidate := ((M.mem_refinementHistoryForcing c.carrier T stages packed _).1 condition).1
  have selectedCandidate := M.assignmentOnIndices_candidate pairing unions powers separation
    (fields 0) hT omega candidate
  obtain ⟨_, hSelected, selectedShape, selectedSmall⟩ :=
    (M.pair_mem_stageOneCandidateBound c.carrier I T row selected).1 selectedCandidate
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨_, closed, children⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  obtain ⟨validSecond, _, secondChildren⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T2 valid2 closed2 symmetric2
  obtain ⟨graphs, hJ, smallJ, validJ, facts⟩ := M.niceAssignmentClassRequests act lower b d alpha T T2 valid
    pairing unions powers separation collection fields infinite choice base directed validSecond closed
    children secondChildren hSelected selectedShape selectedSmall
  refine ⟨hSelected, selectedSmall, graphs, hJ, smallJ, validJ, facts, ?_⟩
  intro C E U Rf Rc idx u w hu hw inA side y
  have inSelected : stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ selected :=
    (mem_assignmentOnIndices I T A _).2 ⟨inA,
      (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨idx, hu, hw⟩⟩
  exact M.niceAssignmentClassGraphs_entry act lower b d alpha T T2 valid pairing unions powers
    separation collection fields hSelected C E U Rf Rc idx u w hu hw inSelected side y

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

theorem semanticStructuralPrefix_fixedIndexClassFamilies
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let I := M.niceRefinementIndices act lower b d alpha T T2 valid
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
    let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    idx ∈ I →
    let oldPairs := fixedIndexAssignmentPairs idx T A
    let bound := M.groundRelations T lower.carrier
    let originalGraphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid
      (assignmentOnIndices I T A)
    let graphs := fun side => fixedIndexAssignmentClassGraph idx T A bound (originalGraphs side)
    let images := fun side => relationImage oldPairs bound (graphs side)
    oldPairs ∈ M.sets ∧ M.groundEmbeddable oldPairs ZFSet.omega ∧
    ∀ side : Fin 2, graphs side ∈ M.sets ∧ ZFSet.IsFunc oldPairs bound (graphs side) ∧
      images side ∈ M.sets ∧ M.groundEmbeddable (images side) ZFSet.omega ∧
      (∀ z ∈ images side, IsName lower z) ∧
      (∀ z, z ∈ images side ↔ ∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
        stageOneAssignment idx v.val w.val ∈ A ∧
        z = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) v (fun _ => w) side)).val) ∧
      (∀ (v w : Name lower), v.val ∈ T → w.val ∈ T →
        stageOneAssignment idx v.val w.val ∈ A → ∀ z,
        ZFSet.pair (ZFSet.pair v.val w.val) z ∈ graphs side ↔
        z = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) v (fun _ => w) side)).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let I := M.niceRefinementIndices act lower b d alpha T T2 valid
  dsimp only
  intro C E U Rf Rc inI
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let oldPairs := fixedIndexAssignmentPairs idx T A
  let bound := M.groundRelations T lower.carrier
  let selected := assignmentOnIndices I T A
  let originalGraphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid selected
  let graphs := fun side => fixedIndexAssignmentClassGraph idx T A bound (originalGraphs side)
  let images := fun side => relationImage oldPairs bound (graphs side)
  obtain ⟨_, _, original, _, _, validImages, _, entries⟩ :=
    M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice condition
  have candidate := ((M.mem_refinementHistoryForcing c.carrier T stages packed _).1 condition).1
  obtain ⟨_, hA, _, smallA⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  have hIdx : idx ∈ M.sets := M.refinementIndexCode_mem pairing hAlpha
    (M.transitive nodes (b.encode_mem C)) (M.transitive nodes (b.encode_mem E))
    U.property Rf.property Rc.property
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hBound := M.groundRelations_mem pairing unions powers separation hT hQ
  obtain ⟨hPairs, smallPairs⟩ := M.fixedIndexAssignmentPairs_mem_small pairing unions powers separation
    choice hIdx hT hA omega smallA
  have covered (v : ZFSet.{u}) (hv : v ∈ T) (w : ZFSet.{u}) (hw : w ∈ T)
      (old : stageOneAssignment idx v w ∈ A) : stageOneAssignment idx v w ∈ selected :=
    (assignmentOnIndices_entry _ _ _ _ _ _).2 ⟨old, inI, hv, hw⟩
  refine ⟨hPairs, smallPairs, ?_⟩
  intro side
  have graphGround : graphs side ∈ M.sets := M.fixedIndexAssignmentClassGraph_mem pairing unions powers
    separation hIdx hT hA hBound (original side).1
  have function : ZFSet.IsFunc oldPairs bound (graphs side) :=
    fixedIndexAssignmentClassGraph_function (original side).2 covered
  have exactEntry (v w : Name lower) (hv : v.val ∈ T) (hw : w.val ∈ T)
      (old : stageOneAssignment idx v.val w.val ∈ A) (z : ZFSet.{u}) :
      ZFSet.pair (ZFSet.pair v.val w.val) z ∈ graphs side ↔
        z = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) v (fun _ => w) side)).val := by
    rw [fixedIndexAssignmentClassGraph_entry]
    have entry := entries C E U Rf Rc inI v w hv hw old side z
    constructor
    · intro edge
      exact entry.1 edge.2.2.2.2
    · intro equal
      have edge := entry.2 equal
      exact ⟨hv, hw, old, (ZFSet.pair_mem_prod.1 ((original side).2.1 edge)).2, edge⟩
  have imageSubset : images side ⊆ relationImage selected bound (originalGraphs side) := by
    intro z hz
    obtain ⟨hy, pair, hp, edge⟩ := (mem_relationImage _ _ _ z).1 hz
    have pb := (mem_relationImage _ _ _ pair).1 hp |>.1
    obtain ⟨v, hv, w, hw, rfl⟩ := ZFSet.mem_prod.1 pb
    have fields := (fixedIndexAssignmentClassGraph_entry _ _ _ _ _ _ _ _).1 edge
    exact (mem_relationImage _ _ _ z).2 ⟨hy, _, covered v hv w hw fields.2.2.1, fields.2.2.2.2⟩
  refine ⟨graphGround, function, M.relationImage_mem separation hPairs hBound graphGround,
    M.groundEmbeddable_function_image pairing unions powers separation choice hPairs hBound omega
      graphGround function smallPairs, ?_, ?_, exactEntry⟩
  · intro z hz
    apply validImages z
    have liftImage : ∀ side : Fin 2, ∀ z, z ∈ relationImage selected bound (originalGraphs side) →
        z ∈ relationImage selected bound (originalGraphs 0) ∪ relationImage selected bound (originalGraphs 1) :=
      Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inl hz))
        (Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inr hz)) (fun j => Fin.elim0 j))
    exact liftImage side z (imageSubset hz)
  · intro z
    constructor
    · intro hz
      obtain ⟨_, pair, hp, edge⟩ := (mem_relationImage _ _ _ z).1 hz
      have pb := (mem_relationImage _ _ _ pair).1 hp |>.1
      obtain ⟨v, hv, w, hw, rfl⟩ := ZFSet.mem_prod.1 pb
      have old := (mem_fixedIndexAssignmentPairs idx T A v w).1 hp |>.2.2
      let vName : Name lower := ⟨v, valid v hv⟩
      let wName : Name lower := ⟨w, valid w hw⟩
      exact ⟨vName, wName, hv, hw, old, (exactEntry vName wName hv hw old z).1 edge⟩
    · rintro ⟨v, w, hv, hw, old, equal⟩
      have edge := (exactEntry v w hv hw old z).2 equal
      exact (mem_relationImage _ _ _ z).2
        ⟨(ZFSet.pair_mem_prod.1 (function.1 edge)).2, ZFSet.pair v.val w.val,
          (mem_fixedIndexAssignmentPairs _ _ _ _ _).2 ⟨hv, hw, old⟩, edge⟩

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

local notation "upperQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "upperOrder" => M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed

theorem semanticStructuralPrefix_preparationEvent_certificates
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A r k enumerations : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row A))
      (ZFSet.pair r (ZFSet.pair k enumerations)) ∈
      M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    let J := M.storedPreparationRequests A fields
    J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
    k ∈ M.sets ∧ enumerations ∈ M.sets ∧
    ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
      (M.groundRelations T upperQ)) k ∧
    ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
      (M.groundRelations T upperQ)) enumerations ∧
    ∃ q, r ∈ upperQ ∧ q ∈ fields 7 ∧
      ZFSet.pair r (ZFSet.pair row A) ∈ upperOrder ∧
      ZFSet.pair r q ∈ rowAssignmentCutGraph upperQ (fields 7)
        (refinementDataHistoryLevels stages packed T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
        ZFSet.omega J
        (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
        (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  obtain ⟨_, condition, _, other, otherStored, terms, nodeCarrier, meetCode, _code⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed upperQ upperOrder b.carrier T alpha
      (ZFSet.pair row A) (ZFSet.pair r (ZFSet.pair k enumerations))).1 entry
  have same : other = fields := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique otherStored stored)
  subst other
  obtain ⟨chosenK, chosenEnumerations, q, payload, hk, he, hr, hq, below, cut, family⟩ :=
    M.varyingPreparation_visit_certificates stages packed upperQ upperOrder b.carrier T alpha
      row A r (ZFSet.pair k enumerations) (canonicalMeetGraph (fields 10) (fields 11)) _ fields
      (run).carriers.data.function.to_isFunc member stored terms nodeCarrier meetCode entry
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 payload
  have requests := M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice condition
  have hJ : M.storedPreparationRequests A fields ∈ M.sets := requests.2.2.2.1
  have smallJ : M.groundEmbeddable (M.storedPreparationRequests A fields) ZFSet.omega :=
    requests.2.2.2.2.1
  exact ⟨hJ, smallJ, hk, he, family.1, family.2.1, q, hr, hq, below, cut, family⟩

theorem semanticStructuralPrefix_preparationEvent_certificate_domain
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {p y : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed upperQ upperOrder b.carrier T) :
    ∃ r k enumerations J N, y = ZFSet.pair r (ZFSet.pair k enumerations) ∧
      N = M.groundRelations T upperQ ∧
      J ∈ M.sets ∧ N ∈ M.sets ∧ k ∈ M.sets ∧ enumerations ∈ M.sets ∧
      M.groundEmbeddable J ZFSet.omega ∧
      ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier N) k ∧
      ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier N) enumerations := by
  obtain ⟨_, hp, hy, _⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed upperQ upperOrder b.carrier T alpha p y).1 entry
  obtain ⟨row, _hRow, A, _hA, rfl⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T stages packed hp)
  obtain ⟨r, _hr, tail, hTail, rfl⟩ := ZFSet.mem_prod.1 hy
  obtain ⟨k, _hkBound, enumerations, _heBound, rfl⟩ := ZFSet.mem_prod.1 hTail
  have certificates := M.semanticStructuralPrefix_preparationEvent_certificates c a t b d
    base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2
    closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
    infinite choice entry
  obtain ⟨hJ, smallJ, hk, he, function, enumerated, _rest⟩ := certificates
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hUpper := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  exact ⟨r, k, enumerations, _, M.groundRelations T upperQ, rfl, rfl, hJ,
    M.groundRelations_mem pairing unions powers separation hT hUpper, hk, he, smallJ,
    function, enumerated⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

noncomputable def fixedIndexOldFineClassImage
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (idx A : ZFSet.{u}) : ZFSet.{u} :=
  let I := M.niceRefinementIndices a s b d level T T2 valid
  let bound := M.groundRelations T s.carrier
  let graph := M.niceAssignmentClassGraphs a s b d level T T2 valid (assignmentOnIndices I T A) 1
  relationImage (fixedIndexAssignmentPairs idx T A) bound
    (fixedIndexAssignmentClassGraph idx T A bound graph)

noncomputable def fixedIndexAugmentedRequests
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (idx A : ZFSet.{u})
    (Rc u : Name s) : ZFSet.{u} :=
  insert (Name.refinementClass T valid Rc u).val
    (M.fixedIndexOldFineClassImage a s b d level T T2 valid idx A)

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

theorem semanticStructuralPrefix_augmentedClassRequests
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc u : (M.nameDomain lower).names),
    let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid → u.val.val ∈ T →
    let oldFine := M.fixedIndexOldFineClassImage act lower b d alpha T T2 valid idx A
    let J := M.fixedIndexAugmentedRequests act lower b d alpha T T2 valid idx A Rc.val u.val
    oldFine ∈ M.sets ∧ M.groundEmbeddable oldFine ZFSet.omega ∧
    J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
    (∀ z ∈ J, IsName lower z) ∧ J ⊆ M.groundRelations T lower.carrier ∧
    (∀ z : Name lower, z.val ∈ J →
      HereditarilySymmetric act lower (d.principalSupportFamily base directed) z ∧
      (∃ V : L, d.principalFix V ≤ (act).stabilizer lower z) ∧
      z.val ⊆ ZFSet.prod T lower.carrier ∧
      ∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
    (∀ z, z ∈ oldFine ↔ ∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
      stageOneAssignment idx v.val w.val ∈ A ∧ z = (Name.refinementClass T valid Rf.val w).val) ∧
    (∀ z, z ∈ J ↔ z = (Name.refinementClass T valid Rc.val u.val).val ∨
      ∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
        stageOneAssignment idx v.val w.val ∈ A ∧ z = (Name.refinementClass T valid Rf.val w).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  dsimp only
  intro C E U Rf Rc u idx hu
  let index := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let oldFine := M.fixedIndexOldFineClassImage act lower b d alpha T T2 valid index A
  let J := M.fixedIndexAugmentedRequests act lower b d alpha T T2 valid index A Rc.val u.val
  obtain ⟨_, _, families⟩ := M.semanticStructuralPrefix_fixedIndexClassFamilies c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
    nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice condition C E U Rf Rc idx
  obtain ⟨_, _, oldGround, oldSmall, _, oldEntry, _⟩ := families 1
  have exactOld (z : ZFSet.{u}) : z ∈ oldFine ↔ ∃ v w : Name lower,
      v.val ∈ T ∧ w.val ∈ T ∧ stageOneAssignment index v.val w.val ∈ A ∧
        z = (Name.refinementClass T valid Rf.val w).val := oldEntry z
  have system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hLower : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hAlpha
      (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have objects := (M.niceRefinementObjects act lower b d base directed pairing unions powers separation
    collection hAlpha hT hT2 hLower lowerOrder nodes nodeOrder system.inputs.terms_closed
    system.terms_hs system.first system.second).2 C E U Rf Rc idx
  have coarseGround := (objects.classes u.val hu).2.1
  have coarseHS := (objects.classes u.val hu).2.2.2
  have jGround : J ∈ M.sets := M.insert_mem pairing unions coarseGround oldGround
  have jSmall : M.groundEmbeddable J ZFSet.omega :=
    M.groundEmbeddable_insert pairing unions powers separation infinite oldGround coarseGround oldSmall
  have exactJ (z : ZFSet.{u}) : z ∈ J ↔
      z = (Name.refinementClass T valid Rc.val u.val).val ∨ ∃ v w : Name lower,
        v.val ∈ T ∧ w.val ∈ T ∧ stageOneAssignment index v.val w.val ∈ A ∧
          z = (Name.refinementClass T valid Rf.val w).val := by
    change z ∈ insert (Name.refinementClass T valid Rc.val u.val).val oldFine ↔ _
    rw [ZFSet.mem_insert_iff, exactOld]
  have classFacts (z : ZFSet.{u}) (hz : z ∈ J) :
      ∃ name : Name lower, z = name.val ∧
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) name ∧
        name.val ⊆ ZFSet.prod T lower.carrier := by
    rcases (exactJ z).1 hz with equal | ⟨v, w, _hv, hw, _old, equal⟩
    · exact ⟨Name.refinementClass T valid Rc.val u.val, equal, coarseHS,
        Name.refinementClass_subset T valid Rc.val u.val⟩
    · exact ⟨Name.refinementClass T valid Rf.val w, equal, (objects.classes w hw).2.2.1,
        Name.refinementClass_subset T valid Rf.val w⟩
  refine ⟨oldGround, oldSmall, jGround, jSmall, ?_, ?_, ?_, exactOld, exactJ⟩
  · intro z hz
    obtain ⟨name, rfl, _, _⟩ := classFacts z hz
    exact name.property
  · intro z hz
    obtain ⟨name, rfl, _, bound⟩ := classFacts z hz
    exact (M.mem_groundRelations T lower.carrier name.val).2 ⟨M.transitive jGround hz, bound⟩
  · intro z hz
    obtain ⟨name, equal, hsName, bound⟩ := classFacts z.val hz
    have same : z = name := Subtype.ext equal
    subst name
    exact ⟨hsName, hsName.symmetric, bound,
      fun H => Name.eval_subset_familySet_of_code_subset H T valid z bound⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
