import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAssignmentLabelDomainTotality
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAugmentedClassRequests
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPreparedWitnessSelections
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparedAlignedReferenceCollisions

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

theorem semanticStructuralPrefix_preparationEnvironment (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed) :
    StoredPreparationEnvironment M fields := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have exactStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same : fields = M.refinementLevelFormulaData act lower b d alpha T T2 valid :=
    refinementFormulaDataCode_injective ((run).carriers.data.function.unique stored exactStored)
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have members : ∀ j, fields j ∈ M.sets := M.refinementFormulaDataCode_fields_mem fields
    (M.transitive (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion stored))
  refine ⟨?_, members, ?_, ?_⟩
  · rw [same]
    exact lower.conditionOrder_code
  · rw [same]
    intro z hz
    exact Name.isName_of_subset valid ((M.mem_groundRelations T lower.carrier z).1 hz).2
  · rw [same]
    intro v V entry _
    obtain ⟨i, equal⟩ := (M.mem_niceVisibilityGraph act lower b T d.principalFix
      (ZFSet.pair v V)).1 entry
    have value := (ZFSet.pair_inj.1 equal).2
    rw [value]
    exact (M.niceVisibilityName act lower T (d.principalFix i)).property

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

theorem semanticStructuralPrefix_assignmentClassRequest_mem
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
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ fields 0 →
      ∀ (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∀ side : Fin 2,
      let request := Name.refinementClass T valid
        (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
        (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
      request.val ∈ M.storedPreparationRequests A fields ∧ request.val ∈ M.sets ∧
      IsName lower request.val ∧
      HereditarilySymmetric act lower (d.principalSupportFamily base directed) request ∧
      ∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} request ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let I := M.niceRefinementIndices act lower b d alpha T T2 valid
  let selected := assignmentOnIndices I T A
  let graphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
  obtain ⟨_hSelected, _smallSelected, functions, hJ, _smallJ, validJ, facts, entries⟩ :=
    M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
      nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
      symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice condition
  dsimp only
  intro C E U Rf Rc idx u w hu hw inA side
  let request := Name.refinementClass T valid
    (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
    (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
  let assignment := stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
    U.val.val Rf.val.val Rc.val.val) u.val w.val
  have inSelected : assignment ∈ selected :=
    (mem_assignmentOnIndices I T A assignment).2 ⟨inA,
      (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨idx, hu, hw⟩⟩
  have edge : ZFSet.pair assignment request.val ∈ graphs side :=
    (entries C E U Rf Rc idx u w hu hw inA side request.val).2 rfl
  have bounded : request.val ∈ bound :=
    (ZFSet.pair_mem_prod.1 ((functions side).2.1 edge)).2
  have image : request.val ∈ relationImage selected bound (graphs side) :=
    (mem_relationImage selected bound (graphs side) request.val).2
      ⟨bounded, assignment, inSelected, edge⟩
  have inJ : request.val ∈ J := by
    have sideCases : side = 0 ∨ side = 1 := by omega
    rcases sideCases with zero | one
    · exact ZFSet.mem_union.2 (Or.inl (zero ▸ image))
    · exact ZFSet.mem_union.2 (Or.inr (one ▸ image))
  have actual : request.val ∈ M.storedPreparationRequests A
      (M.refinementLevelFormulaData act lower b d alpha T T2 valid) := by
    rw [M.storedPreparationRequests_typed]
    exact inJ
  exact ⟨actual, M.transitive hJ inJ, validJ request.val inJ, facts request inJ⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
private theorem selectedFamilyCertificate
    (M : TransitiveGround.{u})
    {P order q nodes nodeOrder meet N visibility top omega J W k enumerations z : ZFSet.{u}}
    (family : PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top
      omega J (M.supportedEqualityCertificateBound nodes W)
      (M.synchronizedEnumerationBound nodes W) k enumerations)
    (member : z ∈ J) :
    ∃ F B f e names, F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
      e ∈ M.sets ∧ names ∈ M.sets ∧
      ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
      ZFSet.pair z (ZFSet.pair e names) ∈ enumerations ∧
      PreparedCertificateCode M P order q nodes nodeOrder meet N visibility top omega z F B f e names := by
  obtain ⟨value, edge, _unique⟩ := family.1.2 z member
  have bounded := (ZFSet.pair_mem_prod.1 (family.1.1 edge)).2
  obtain ⟨F, hF, tail, hTail, rfl⟩ := ZFSet.mem_prod.1 bounded
  obtain ⟨B, hB, f, hf, rfl⟩ := ZFSet.mem_prod.1 hTail
  obtain ⟨value, enumerated, _unique⟩ := family.2.1.2 z member
  have bounded := (ZFSet.pair_mem_prod.1 (family.2.1.1 enumerated)).2
  obtain ⟨e, he, names, hn, rfl⟩ := ZFSet.mem_prod.1 bounded
  exact ⟨F, B, f, e, names, ((M.mem_groundPower nodes F).1 hF).1,
    ((M.mem_groundSmallSubsets nodes ZFSet.omega B).1 hB).1,
    ((M.mem_groundRelations nodes W f).1 hf).1,
    ((M.mem_groundRelations ZFSet.omega nodes e).1 he).1,
    ((M.mem_groundRelations ZFSet.omega W names).1 hn).1, edge, enumerated,
    family.2.2 z F B f e names edge enumerated⟩

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

theorem semanticStructuralPrefix_prepared_assignment_certificates
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ fields 0 →
      ∀ (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ upperQ ∧
        sourceA ⊆ A ∧
      ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q ∈ fields 7,
        ZFSet.pair (ZFSet.pair row A) q ∈ rowAssignmentCutGraph upperQ (fields 7)
          (refinementDataHistoryLevels stages packed T) alpha ∧
        PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
          (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
          ZFSet.omega (M.storedPreparationRequests sourceA fields)
          (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
          (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations ∧
      ∀ side : Fin 2,
        let request := Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
        request.val ∈ M.storedPreparationRequests sourceA fields ∧ request.val ∈ M.sets ∧
        IsName lower request.val ∧
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) request ∧
        (∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} request ⊆
          Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
        ∃ F B f e names, F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
          e ∈ M.sets ∧ names ∈ M.sets ∧
          ZFSet.pair request.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
          ZFSet.pair request.val (ZFSet.pair e names) ∈ enumerations ∧
          PreparedCertificateCode M (fields 7) (fields 8) q (fields 10) (fields 11)
            (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
            ZFSet.omega request.val F B f e names := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  dsimp only
  intro C E U Rf Rc idx u w hu hw inA
  let index := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let x := stageOneAssignment index u.val w.val
  obtain ⟨beta, _hBeta, other, otherStored, terms, _nodeCarrier, _meet, _environment,
      sourceRow, sourceA, hSourceA, sourceCondition, sourceSubset, selected,
      k, hk, enumerations, he, q, hq, cut, family⟩ := prepared row A rfl x inA
  have inSource := (mem_assignmentOnIndices (other 0) T sourceA x).1 selected
  have indexOther := (stageOneAssignment_mem_assignments (other 0) T index u.val w.val).1 inSource.2
  have alphaEdge := (run).carriers.data.coverage alpha member fields stored index idx
    u.val hu w.val hw
  have betaEdge := (run).carriers.data.coverage beta _hBeta other otherStored index indexOther.1
    u.val (terms.symm ▸ hu) w.val (terms.symm ▸ hw)
  have equal : beta = alpha := by
    have fn := (run).carriers.data.levels_function
    have hx := (ZFSet.pair_mem_prod.1 (fn.1 alphaEdge)).1
    obtain ⟨_, _, unique⟩ := fn.2 x hx
    exact (unique _ betaEdge).trans (unique _ alphaEdge).symm
  subst beta
  have same : other = fields := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique otherStored stored)
  subst other
  refine ⟨sourceRow, sourceA, hSourceA, sourceCondition, sourceSubset, k, hk,
    enumerations, he, q, hq, cut, family, ?_⟩
  intro side
  let request := Name.refinementClass T valid
    (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
    (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
  have facts := M.semanticStructuralPrefix_assignmentClassRequest_mem c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice
    sourceCondition C E U Rf Rc idx u w hu hw inSource.1 side
  exact ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2,
    selectedFamilyCertificate M family facts.1⟩

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

theorem semanticStructuralPrefix_typed_assignment_certificates
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ fields 0 →
      ∀ (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ upperQ ∧
        sourceA ⊆ A ∧
      ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q : SetMembers Q,
        ZFSet.pair (ZFSet.pair row A) (lower.encode q) ∈ rowAssignmentCutGraph upperQ (fields 7)
          (refinementDataHistoryLevels stages packed T) alpha ∧
        PreparedCertificateFamilyCode M (fields 7) (fields 8) (lower.encode q) (fields 10) (fields 11)
          (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
          ZFSet.omega (M.storedPreparationRequests sourceA fields)
          (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
          (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations ∧
      ∀ side : Fin 2,
        let request := Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
        request.val ∈ M.storedPreparationRequests sourceA fields ∧ request.val ∈ M.sets ∧
        IsName lower request.val ∧
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) request ∧
        (∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} request ⊆
          Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
        ∃ F B f e names, F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
          e ∈ M.sets ∧ names ∈ M.sets ∧
          ZFSet.pair request.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
          ZFSet.pair request.val (ZFSet.pair e names) ∈ enumerations ∧
          PreparedCertificateCode M (fields 7) (fields 8) (lower.encode q) (fields 10) (fields 11)
            (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
            ZFSet.omega request.val F B f e names ∧
          M.TypedPreparedCertificate act lower b T d.principalFix (fields 11)
            (canonicalMeetGraph (fields 10) (fields 11)) ZFSet.omega request q F B f e names := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have environment := M.semanticStructuralPrefix_preparationEnvironment c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member fields stored
  dsimp only
  intro C E U Rf Rc idx u w hu hw inA
  obtain ⟨sourceRow, sourceA, hSourceA, sourceCondition, sourceSubset,
      k, hk, enumerations, he, rawq, hq, cut, family, selected⟩ :=
    M.semanticStructuralPrefix_prepared_assignment_certificates c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice prepared C E U Rf Rc idx u w hu hw inA
  obtain ⟨q, rfl⟩ := (lower.mem_carrier rawq).1 hq
  refine ⟨sourceRow, sourceA, hSourceA, sourceCondition, sourceSubset,
    k, hk, enumerations, he, q, cut, family, ?_⟩
  intro side
  obtain ⟨requestMember, requestGround, requestValid, requestHS, requestSubset,
    F, B, f, e, names, hF, hB, hf, he, hn, kEdge, enumEdge, rawCode⟩ := selected side
  refine ⟨requestMember, requestGround, requestValid, requestHS, requestSubset,
    F, B, f, e, names, hF, hB, hf, he, hn, kEdge, enumEdge, rawCode, ?_⟩
  exact M.preparedCertificateCode_typed act lower b T d.principalFix pairing unions powers
    separation collection (environment.ground 7) (environment.ground 8) hT valid
    (environment.ground 13) (fields 11) (canonicalMeetGraph (fields 10) (fields 11))
    ZFSet.omega ⟨_, requestGround⟩ q F B f e names rawCode

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
local notation "levels" => refinementDataHistoryLevels stages packed T
local notation "image" => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace

theorem semanticStructuralPrefix_aligned_copy_crossCollisions
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r oldRow row : R) (A oldA : ZFSet.{u}) (g h : G) (D X V : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair (c.encode r) A))
    (belowOld : row ≤ oldRow) (oldBelowG : oldRow ≤ a.iso g r) (belowH : row ≤ a.iso h r)
    (contains : image (t.encode g) A ⊆ oldA)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (overlap : meet (d.iso h D) X = d.iso h V)
    (meetLeft : meet (d.iso h D) X ≤ d.iso h D)
    (meetRight : meet (d.iso h D) X ≤ X)
    (meetGreatest : ∀ z : L, z ≤ d.iso h D → z ≤ X → z ≤ meet (d.iso h D) X) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    ∀ (_descent : ∀ (H : ConditionFilter (SetMembers Q)),
      H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
      ∀ (v w : L) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ (act).stabilizer lower x.val →
        d.principalFix w ≤ (act).stabilizer lower y.val →
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) x.val →
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ tau : (M.nameDomain lower).names,
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau.val ∧
          d.principalFix (meet v w) ≤ (act).stabilizer lower tau.val ∧
          Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val),
      (∀ z ∈ image (t.encode h) A, ZFSet.pair z (b.encode (d.iso h D)) ∈
        stageOneDataBounds (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
          (refinementIndexFieldGraph I b.carrier 2) tuples) →
      (∀ z ∈ oldA, ZFSet.pair z (b.encode X) ∈
        stageOneDataBounds oldA I T S b.carrier mu positions b.conditionOrder
          (refinementIndexFieldGraph I b.carrier 2) tuples) →
      ZFSet.pair (c.encode row) (assignmentCut levels alpha (image (t.encode h) A ∪ oldA)) ∈ Q →
      stageOneRawCrossCollisions M fields (image (t.encode h) A) oldA
        (ZFSet.pair (c.encode row) (assignmentCut levels alpha (image (t.encode h) A ∪ oldA))) := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  dsimp only
  intro descent newData oldData validCut
  have system := M.semanticStructuralPrefix_stageSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have canonicalStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have environment := M.semanticStructuralPrefix_preparationEnvironment c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member fields canonicalStored
  have hQ : lower.carrier ∈ M.sets := environment.ground 7
  have orderGround : lower.conditionOrder ∈ M.sets := environment.ground 8
  obtain ⟨stage, stored⟩ := trace.1.total member
  have sameStage := (trace.2 alpha member stage stored).trans
    (M.semanticStructuralPrefix_stageCode c a t b d base directed T T2 rowTop pairing unions powers
      separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps
      supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows
      hh ordinal trace hAlpha cutOrdinal subset)
  have exactStored : ZFSet.pair alpha
      (forcingStageCode lower.carrier lower.conditionOrder (lower.encode ⊤) ((act).actionGraph lower t))
      ∈ history := sameStage ▸ stored
  let localImage := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, localImage g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  have liftedSupport (Z : L) := a.positionSupport_of_codeLift c.pairEmpty act lower
    (M.refinementHistoryRowNameLift c ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier)
    (M.refinementHistoryRowNameLift_val c ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier)
    (M.refinementHistoryRowNameLift_stabilizer c ((run).carriers.restrict cutOrdinal subset) cutOrdinal
      carrier a act localImage coordinates emptyImage)
    T valid1 b d S mu positions tuples Z range (support Z)
  let qStrong : SetMembers Q := SetMembers.ofMem _ validCut
  have strongCode : lower.encode qStrong = ZFSet.pair (c.encode row)
      (assignmentCut levels alpha (image (t.encode h) A ∪ oldA)) := SetMembers.raw_ofMem _ _
  intro sharedIdx hi rawU hu rawOldU hOldU rawW hw rawOldW hOldW newMember oldMember
  have newBound := newData _ newMember
  have oldBound := oldData _ oldMember
  obtain ⟨C, E, U, Rf, Rc, u, w, index, hu0, hw0, original, indexEq, termU, termW, edge⟩ :=
    M.semanticStructuralPrefix_assignmentImage_decode c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member h A sharedIdx rawU rawW hi hu hw newMember
  subst sharedIdx rawU rawW
  let oldU : (M.nameDomain lower).names := ⟨⟨rawOldU, valid rawOldU hOldU⟩, M.transitive hT hOldU⟩
  let oldW : (M.nameDomain lower).names := ⟨⟨rawOldW, valid rawOldW hOldW⟩, M.transitive hT hOldW⟩
  obtain ⟨_sourceRow, _sourceA, _hSourceA, _sourceCondition, _sourceSubset,
      _k, _hk, _enumerations, _he, qOriginal, cut, _family, selected⟩ :=
    M.semanticStructuralPrefix_typed_assignment_certificates c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice prepared C E U Rf Rc index u.val w.val hu0 hw0 original
  obtain ⟨_, _, _, _, _, F0, B0, f0, e0, names0, _, _, _, _, _, _k0, _enum0, code0, _typed0⟩ := selected 0
  obtain ⟨_, _, _, _, _, F1, B1, f1, e1, names1, _, _, _, _, _, _k1, _enum1, code1, _typed1⟩ := selected 1
  have testFacts := M.semanticStructuralPrefix_aligned_cut_tests c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member r oldRow row A oldA g h source oldSource
    belowOld oldBelowG belowH contains qOriginal qStrong cut strongCode
  have collisions := M.structuralAssignment_prepared_aligned_collision act lower t b d base directed alpha T T2
    system pairing unions powers separation collection hQ orderGround group nodes supports hAlpha hT meet descent
    small trace.1 exactStored I S mu positions tuples A (image (t.encode h) A) oldA liftedSupport
    g h D X V C E U Rf Rc u w oldU oldW index hu0 hw0 hOldU hOldW qOriginal qStrong
    testFacts.2.2.1 testFacts.2.2.2 relative overlap meetLeft meetRight meetGreatest
    ![F0, F1] ![B0, B1] ![f0, f1] ![e0, e1] ![names0, names1]
    original edge newBound oldBound contains testFacts.1 testFacts.2.1
    (Fin.cases code0 (Fin.cases code1 (fun j => Fin.elim0 j)))
  rw [strongCode] at collisions
  exact collisions

end PartitionPilot.Forcing.TransitiveGround

end OAI
