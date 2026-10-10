import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAlignedLargerCutTests
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralRefinementNormalization
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRefinementAssignmentLabelNames
import OAI.SetTheory.PartitionPrinciple.Forcing.RefinementAssignmentLabelActions
import OAI.SetTheory.PartitionPrinciple.Forcing.RefinementDataBoundActions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundAssignmentLabelDomainTotality

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

theorem semanticStructuralPrefix_stageSystem :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    RefinementStageSystem M act lower t b d base directed alpha T T2 := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have hGraph : (act).actionGraph lower t ∈ M.sets := by
    rw [M.semanticStructuralPrefixAction_graph]
    have ground := M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hAlpha hh omega
    unfold structuralForcingCarrier at ground
    rw [M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 subset] at ground
    exact ground
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1
    closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  exact M.recursiveRefinementStageSystem c a t b d base directed T T2 alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal pairing unions powers separation collection
    carrier rowOrderGround group nodes nodeOrder nodeMaps supports hT hT2 hAlpha hLowerPacked
    omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 rowTop topMem topRows
    act image coordinates emptyImage hGraph

theorem semanticStructuralPrefix_assignmentImage_decode :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    ∀ (h : G) (A sharedIdx rawU rawW : ZFSet.{u}), sharedIdx ∈ fields 0 →
      rawU ∈ T → rawW ∈ T →
      stageOneAssignment sharedIdx rawU rawW ∈
        M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) A →
    ∃ (C E : L) (U Rf Rc u w : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ fields 0 ∧
      u.val.val ∈ T ∧ w.val.val ∈ T ∧
      stageOneAssignment
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val ∈ A ∧
      sharedIdx = refinementIndexCode alpha (b.encode (d.iso h C)) (b.encode (d.iso h E))
        ((act).act lower h U.val).val ((act).act lower h Rf.val).val ((act).act lower h Rc.val).val ∧
      rawU = ((act).act lower h u.val).val ∧ rawW = ((act).act lower h w.val).val ∧
      ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val.val w.val.val)) (stageOneAssignment sharedIdx rawU rawW) ∈
        M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have orderGround : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  obtain ⟨stage, stored⟩ := trace.1.total member
  have same := (trace.2 alpha member stage stored).trans
    (M.semanticStructuralPrefix_stageCode c a t b d base directed T T2 rowTop pairing unions powers
      separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps
      supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows
      hh ordinal trace hAlpha cutOrdinal subset)
  have exactStored : ZFSet.pair alpha
      (forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t))
      ∈ history := same ▸ stored
  dsimp only
  intro h A sharedIdx rawU rawW index hu hw imageMember
  exact M.structuralAssignmentImage_decode act lower t b d base directed alpha T T2 system
    pairing unions powers separation collection hQ orderGround group nodes supports hAlpha hT
    trace.1 exactStored h A sharedIdx rawU rawW index hu hw imageMember

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u

private theorem storedAssignmentImage_entry
    (M : TransitiveGround.{u}) {G P L : Type u}
    [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
    (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (b : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (level T T2 : ZFSet.{u})
    (system : RefinementStageSystem M a s t b d base directed level T T2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (g : G) (C E : L) (U Rf Rc : (M.nameDomain s).names) (v w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hv : v.val ∈ T) (hw : w.val ∈ T) (A : ZFSet.{u}) :
    stageOneAssignment (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val)
      (a.act s g v).val (a.act s g w).val ∈
      M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A ↔
    stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A := by
  let x := stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
    U.val.val Rf.val.val Rc.val.val) v.val w.val
  let y := stageOneAssignment (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
    (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val)
    (a.act s g v).val (a.act s g w).val
  have dataEq := M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps level T T2 system.valid1 system.valid2
  have graphEq := M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers
    separation collection carrier group nodes order system.inputs.condition_maps system.inputs.node_maps
    supports level T T2 hLevel hT system.valid1 system.valid2 system.inputs.terms_closed
    system.inputs.pairs_closed system.inputs.family_ground system.indices.index_ground g
  have entry : ZFSet.pair x y ∈ M.refinementAssignmentActionGraph a s b d level T T2
      system.valid1 system.valid2 g :=
    (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1 system.valid2
      system.inputs.terms_closed t pairing unions powers separation collection carrier order
      system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
      g C E U Rf Rc v w index hv hw y).2 rfl
  have rawEntry := graphEq.symm ▸ entry
  have xBranch : x ∈ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
        t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level 0) T := by
    rw [dataEq]
    exact (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨index, hv, hw⟩
  have yBranch := (ZFSet.pair_mem_prod.1
    (M.rawStageRefinementAssignmentActionGraph_branch_bound (t.encode g) s.carrier s.conditionOrder
      (s.encode ⊤) (a.actionGraph s t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 level rawEntry)).2
  have wholeEntry := (M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored xBranch
    (t.encode g) y).2 ⟨t.encode_mem g, rawEntry⟩
  change y ∈ _ ↔ x ∈ A
  rw [M.structuralAssignmentImage_entry]
  constructor
  · rintro ⟨x', hx', edge⟩
    have sourceBranch := (M.structuralAssignmentActionGraph_branch_iff t.carrier b.carrier
      b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
      function stored edge).2 yBranch
    have branch := (M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored sourceBranch
      (t.encode g) y).1 edge |>.2
    rw [graphEq] at branch
    have injection := M.refinementAssignmentActionGraph_injection a s b d level T T2
      system.valid1 system.valid2 t pairing unions powers separation collection carrier order
      system.inputs.condition_maps system.inputs.terms_closed system.inputs.pairs_closed
      system.inputs.family_ground g
    exact injection.injective _ _ _ branch entry ▸ hx'
  · intro hx
    exact ⟨x, hx, wholeEntry⟩

private theorem occurrenceAt_code {Q : Type u} (upper : Presentation Q)
    (p : Q) (row A assignment : ZFSet.{u}) (code : upper.encode p = ZFSet.pair row A) :
    (∃ r B, upper.encode p = ZFSet.pair r B ∧ assignment ∈ B) ↔ assignment ∈ A := by
  constructor
  · rintro ⟨r, B, equal, member⟩
    exact (ZFSet.pair_inj.1 (equal.symm.trans code)).2 ▸ member
  · intro member
    exact ⟨row, A, code, member⟩
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
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace

theorem semanticStructuralAssignment_occurrence_act :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let lower := SetMembers.presentation Q
    let upper := SetMembers.presentation upperQ
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (g : G) (C E : L) (U Rf Rc : (M.nameDomain lower).names) (v w : Name lower),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid → v.val ∈ T → w.val ∈ T →
      ∀ p : SetMembers upperQ,
      (∃ row A, upper.encode ((upperAct).iso g p) = ZFSet.pair row A ∧
        stageOneAssignment (refinementIndexCode alpha (b.encode (d.iso g C)) (b.encode (d.iso g E))
          ((act).act lower g U.val).val ((act).act lower g Rf.val).val ((act).act lower g Rc.val).val)
          ((act).act lower g v).val ((act).act lower g w).val ∈ A) ↔
      (∃ row A, upper.encode p = ZFSet.pair row A ∧
        stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
          U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let lower := SetMembers.presentation Q
  let upper := SetMembers.presentation upperQ
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have orderGround : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  obtain ⟨stage, stored⟩ := trace.1.total member
  have same := (trace.2 alpha member stage stored).trans
    (M.semanticStructuralPrefix_stageCode c a t b d base directed T T2 rowTop pairing unions powers
      separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps
      supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows
      hh ordinal trace hAlpha cutOrdinal subset)
  have exactStored : ZFSet.pair alpha
      (forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t))
      ∈ history := same ▸ stored
  dsimp only
  intro g C E U Rf Rc v w index hv hw p
  obtain ⟨r, A, _, code⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier T stages packed) (SetMembers.raw_mem p)
  have moved := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace g p r A code
  rw [occurrenceAt_code upper _ _ _ _ moved, occurrenceAt_code upper _ _ _ _ code]
  exact storedAssignmentImage_entry M act lower t b d base directed alpha T T2 system
    pairing unions powers separation collection hQ orderGround group nodes supports hAlpha hT
    trace.1 exactStored g C E U Rf Rc v w index hv hw A

theorem semanticStructuralAssignment_occurrence_fixed_index :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let lower := SetMembers.presentation Q
    let upper := SetMembers.presentation upperQ
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (g : G) (C E : L) (U Rf Rc : (M.nameDomain lower).names) (v w : Name lower),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid → v.val ∈ T → w.val ∈ T →
      g ∈ d.principalFix E → ∀ p : SetMembers upperQ,
      (∃ row A, upper.encode ((upperAct).iso g p) = ZFSet.pair row A ∧
        stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
          U.val.val Rf.val.val Rc.val.val) ((act).act lower g v).val ((act).act lower g w).val ∈ A) ↔
      (∃ row A, upper.encode p = ZFSet.pair row A ∧
        stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
          U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let lower := SetMembers.presentation Q
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  dsimp only
  intro g C E U Rf Rc v w index hv hw fixed p
  have same := M.niceRefinementIndex_copies_agree act lower b d alpha T T2 system.valid1 system.valid2
    system.indices C E U Rf Rc index 1 g E le_rfl (by simpa only [inv_one, one_mul] using fixed)
  simp only [d.one, PosetAction.act_one] at same
  have covariance := M.semanticStructuralAssignment_occurrence_act c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member g C E U Rf Rc v w index hv hw p
  rwa [same] at covariance

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L] [OrderBot L]
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

theorem semanticStructuralAssignmentImage_dataBound
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (S mu tuples : ZFSet.{u}) (hS : S ∈ M.sets) (hmu : mu ∈ M.sets)
    (hTuples : tuples ∈ M.sets)
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (tupleAction : ∀ g f, f ∈ S → ∀ tau : Name c.pairEmpty,
      ZFSet.pair f tau.val ∈ tuples →
      rowPositionSequenceAction d b g mu f ∈ S ∧
      ZFSet.pair (rowPositionSequenceAction d b g mu f) (a.act c.pairEmpty g tau).val ∈ tuples) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let I := refinementDataHistoryIndices stages packed
    let anchors := refinementIndexFieldGraph I b.carrier 2
    ∀ (g : G) (D : L) (A : ZFSet.{u}), A ∈ M.sets →
      (∀ z ∈ A, ZFSet.pair z (b.encode D) ∈
        stageOneDataBounds A I T S b.carrier mu b.nonbottom.carrier b.conditionOrder anchors tuples) →
    let movedA := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A
    movedA ∈ M.sets ∧
      stageOneDataBounds movedA I T S b.carrier mu b.nonbottom.carrier b.conditionOrder anchors tuples ∈ M.sets ∧
      ∀ z ∈ movedA, ZFSet.pair z (b.encode (d.iso g D)) ∈
        stageOneDataBounds movedA I T S b.carrier mu b.nonbottom.carrier b.conditionOrder anchors tuples := by
  intro packed I anchors g D A hA bound movedA
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hI := M.refinementDataHistoryIndices_mem pairing unions powers separation hs hPacked
  have hMoved := M.structuralAssignmentImage_mem pairing unions powers separation collection
    group nodes nodeOrder nodeAction supports hT hT2 hs hh (M.transitive group (t.encode_mem g)) hA
  refine ⟨hMoved, M.stageOneDataBounds_mem pairing unions powers separation hMoved hI hT hS nodes hmu
    (M.nonbottom_carrier_mem b separation nodes) nodeOrder
    (M.refinementIndexFieldGraph_mem pairing unions powers separation hI nodes 2) hTuples, ?_⟩
  intro z hz
  obtain ⟨x, hx, edge⟩ := (M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A z).1 hz
  obtain ⟨_, alpha, member, rawP, rawOrder, rawTop, rawAction, stored, branch⟩ :=
    (M.pair_mem_structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) x z).1 edge
  have targetBranch := (ZFSet.pair_mem_prod.1
    (M.rawStageRefinementAssignmentActionGraph_branch_bound (t.encode g) rawP rawOrder rawTop rawAction
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
      T T2 alpha branch)).2
  obtain ⟨idx, idxRaw, rawU, hu, rawW, hw, rfl⟩ := (mem_stageOneAssignments _ _ z).1 targetBranch
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have hAlpha := M.transitive hs member
  have cutOrdinal := ordinalSetProperty_member ordinal member
  have subset := (And.left ordinal) alpha member
  let restricted := run.carriers.restrict cutOrdinal subset
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    restricted cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed))
  let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let valid := M.refinementHistoryRowNameFamily_valid c restricted cutOrdinal carrier T valid1
  have actualEntry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have rawEntry : ZFSet.pair alpha (refinementFormulaDataCode
      (M.rawRefinementFormulaData rawP rawOrder rawTop rawAction t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 alpha)) ∈ packed :=
    (M.pair_mem_structuralRefinementHistory _ _ _ _ _ _ _ _ _ _).2
      ⟨member, rawP, rawOrder, rawTop, rawAction, stored, rfl⟩
  have sameData : M.rawRefinementFormulaData rawP rawOrder rawTop rawAction t.carrier b.carrier
      b.conditionOrder (supportBasisCode b t d.principalFix) T T2 alpha =
      M.refinementLevelFormulaData act lower b d alpha T T2 valid :=
    refinementFormulaDataCode_injective (run.carriers.data.function.unique rawEntry actualEntry)
  have idxNice : idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid := by
    rw [sameData] at idxRaw
    exact idxRaw
  obtain ⟨C, E, U, Rf, Rc, u, w, _sourceIndex, _sourceU, _sourceW, source,
      sameIndex, sameU, sameW, _sourceEdge⟩ :=
    M.semanticStructuralPrefix_assignmentImage_decode c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member g A idx rawU rawW idxNice hu hw hz
  have idxWhole := M.semanticStructuralPrefix_index_mem_history c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member idx idxNice
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  have tupleMoved : ∀ f ∈ S, ∀ tau : Name lower, ZFSet.pair f tau.val ∈ tuples →
      rowPositionSequenceAction d b g mu f ∈ S ∧
      ZFSet.pair (rowPositionSequenceAction d b g mu f) (act.act lower g tau).val ∈ tuples := by
    intro f hf tau entry
    let original : Name c.pairEmpty := ⟨tau.val, valid1 tau.val (range f tau.val entry)⟩
    have same : M.refinementHistoryRowNameLift c restricted cutOrdinal carrier original = tau :=
      Subtype.ext (M.refinementHistoryRowNameLift_val c restricted cutOrdinal carrier original)
    have moved := tupleAction g f hf original entry
    refine ⟨moved.1, ?_⟩
    rw [← same, M.refinementHistoryRowNameLift_act c restricted cutOrdinal carrier
      a act image coordinates emptyImage, M.refinementHistoryRowNameLift_val]
    exact moved.2
  have result := refinementDataBound_act act lower b d I T S mu tuples A movedA alpha g C E D
    U.val Rf.val Rc.val u.val w.val tupleMoved (bound _ source)
    (by rwa [← sameIndex, ← sameU, ← sameW])
    (by rwa [← sameIndex]) (by rwa [← sameU]) (by rwa [← sameW])
  rw [sameIndex, sameU, sameW]
  exact result

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

local notation "liftName" => M.semanticStructuralNameLift c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralAssignmentLabel_supported_hs :
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
      let label := Name.refinementAssignmentLabel upper inc ⊤ T valid
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) Rf Rc
      d.principalFix E ≤ (upperAct).stabilizer upper label ∧
        HereditarilySymmetric upperAct upper (d.principalSupportFamily base directed) label := by
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
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have equivariant : ∀ g p, inc ((lowerAct).iso g p) = (upperAct).iso g (inc p) := fun g p =>
    (M.semanticStructuralInclusion_equivariant c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice g p).symm
  dsimp only
  intro C E U Rf Rc index
  obtain ⟨less, _domainCandidate, fineCandidate, coarseCandidate, _forced⟩ :=
    (system.indices.typed_entries C E U Rf Rc).1 index
  have fine : d.principalFix E ≤ (lowerAct).stabilizer lower Rf.val :=
    (d.principalFix_antitone less.le).trans
      ((M.name_mem_niceNameCandidates lowerAct lower T2 (d.principalFix C) Rf.val).1 fineCandidate).2.2
  have coarse : d.principalFix E ≤ (lowerAct).stabilizer lower Rc.val :=
    (d.principalFix_antitone less.le).trans
      ((M.name_mem_niceNameCandidates lowerAct lower T2 (d.principalFix C) Rc.val).1 coarseCandidate).2.2
  have occurrences := fun g (hg : g ∈ d.principalFix E) (v w : Name lower) (p : SetMembers Q)
      (hv : v.val ∈ T) (hw : w.val ∈ T) =>
    M.semanticStructuralAssignment_occurrence_fixed_index c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member g C E U Rf Rc v w index hv hw hg p
  refine ⟨Name.refinementAssignmentLabel_support lowerAct upperAct lower upper inc equivariant
    T valid system.inputs.terms_closed _ Rf.val Rc.val (d.principalFix E) occurrences fine coarse, ?_⟩
  exact Name.refinementAssignmentLabel_hs lowerAct upperAct lower upper inc equivariant T valid
    system.inputs.terms_closed (d.principalSupportFamily base directed) system.terms_hs _ Rf.val Rc.val
    (d.principalFix E) ⟨E, le_rfl⟩ occurrences fine coarse
    (system.second.candidate_hs C Rf.val fineCandidate) (system.second.candidate_hs C Rc.val coarseCandidate)

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

local notation "liftName" => M.semanticStructuralNameLift c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralAssignmentLabel_ground_supported_hs :
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
      let label := Name.refinementAssignmentLabel upper inc ⊤ T valid
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) Rf Rc
      label.val ∈ M.sets ∧ d.principalFix E ≤ (upperAct).stabilizer upper label ∧
        HereditarilySymmetric upperAct upper (d.principalSupportFamily base directed) label := by
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
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have lowerGround : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hAlpha hLowerPacked omega
  have upperGround : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hs hPacked omega
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha hLowerPacked omega
  have inclusionGround : lower.graph upper inc ∈ M.sets :=
    (run).inclusionFunction_graph_mem ordinal cutOrdinal subset pairing unions powers separation
      hs hPacked hT hAlpha carrier infinite choice rowTop topMem topRows mono omega
  dsimp only
  intro C E U Rf Rc index
  have hIdx := M.refinementIndexCode_mem pairing hAlpha
    (M.transitive nodes (b.encode_mem C)) (M.transitive nodes (b.encode_mem E))
    U.property Rf.property Rc.property
  refine ⟨M.refinementAssignmentLabel_mem lower upper pairing unions powers separation collection
    lowerGround upperGround lowerOrder inc inclusionGround ⊤ T hT valid _ hIdx
    Rf.val Rc.val Rf.property Rc.property, ?_⟩
  exact M.semanticStructuralAssignmentLabel_supported_hs c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice C E U Rf Rc index

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

local notation "liftName" => M.semanticStructuralNameLift c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice

theorem semanticStructuralAssignmentLabel_domain_total :
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
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices lowerAct lower b d alpha T T2 valid →
      ∀ (H : ConditionFilter (SetMembers Q)), H.GenericFor (formulaFamily (M.nameDomain upper)) →
      (∀ u : (M.nameDomain lower).names, u.val.val ∈ T →
        M.representedDomainConditions lower upper.carrier levels alpha T valid idx U Rc u ∈ M.sets ∧
        Dense {p : SetMembers Q | upper.encode p ∈
          M.representedDomainConditions lower upper.carrier levels alpha T valid idx U Rc u}) →
      ∀ z ∈ Name.eval {q | H.mem (inc q)} (Name.refinementQuotient T valid U.val Rc.val),
        ∃ y : ZFSet.{u}, ZFSet.pair z y ∈ Name.eval {p | H.mem p}
          (Name.refinementAssignmentLabel upper inc ⊤ T valid idx Rf.val Rc.val) := by
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
  let restriction := (run).restriction ordinal cutOrdinal subset c.conditionOrder_code
  let inclusion := (run).inclusion ordinal cutOrdinal subset pairing unions powers separation
    infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono c.conditionOrder_code
  have projection : CompleteProjection restriction inclusion :=
    M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice
  have hLowerPacked := M.graphRestriction_mem unions separation hAlpha hPacked
  have lowerGround : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hAlpha hLowerPacked omega
  have upperGround : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hs hPacked omega
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround
      hT hAlpha hLowerPacked omega
  have inclusionGround : lower.graph upper inclusion ∈ M.sets :=
    (run).inclusionFunction_graph_mem ordinal cutOrdinal subset pairing unions powers separation
      hs hPacked hT hAlpha carrier infinite choice rowTop topMem topRows mono omega
  have levelsGround := M.refinementDataHistoryLevels_mem pairing unions powers separation hs hPacked hT
  have cutCoordinates : ∀ p : SetMembers Q, ∃ row A : ZFSet.{u},
      upper.encode p = ZFSet.pair row A ∧
      lower.encode (restriction p) = ZFSet.pair row (assignmentCut levels alpha A) := by
    intro p
    obtain ⟨row, _rowMem, A, _dataMem, code⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape c.carrier T stages packed (SetMembers.raw_mem p))
    exact ⟨row, A, code, (run).restrictionFunction_raw ordinal cutOrdinal subset p row A code⟩
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  dsimp only
  intro C E U Rf Rc index H ordinary density
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  have hIdx : idx ∈ M.sets := M.transitive system.indices.index_ground index
  exact M.refinementAssignmentLabel_domain_total lower upper projection
    pairing unions powers separation collection lowerGround upperGround lowerOrder inclusionGround
    levelsGround hAlpha hT valid idx hIdx U Rc Rf.val cutCoordinates H ordinary density

end PartitionPilot.Forcing.TransitiveGround

end OAI
