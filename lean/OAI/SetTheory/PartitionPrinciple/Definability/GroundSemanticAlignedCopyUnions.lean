import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAlignedCopyCollisions
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticPreparedWitnessSelections
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparedSelectionProfiles
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparedStructuralInsertionCollisions
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRefinementMixedUnions

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

theorem semanticStructuralTrace_mixed_union_extension
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    ∀ row rowA rowB A B : ZFSet.{u},
      ZFSet.pair rowA A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      ZFSet.pair rowB B ∈ M.refinementHistoryForcing c.carrier T stages packed →
      ZFSet.pair row rowA ∈ c.conditionOrder →
      ZFSet.pair row rowB ∈ c.conditionOrder →
      (∀ beta ∈ stages, ∀ data : Fin 15 → ZFSet.{u},
        ZFSet.pair beta (refinementFormulaDataCode data) ∈ packed →
        ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) beta (A ∪ B)) ∈
          M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed) →
        stageOneRawCrossCollisions M data A B (ZFSet.pair row
          (assignmentCut (refinementDataHistoryLevels stages packed T) beta (A ∪ B)))) →
      ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowA A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowB B) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  dsimp only
  intro row rowA rowB A B first second rowBelowA rowBelowB cross
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact run.mixed_union_extension pairing unions powers separation infinite choice hs hPacked hT
    ordinal mono c.conditionOrder_code first second rowBelowA rowBelowB cross

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

local notation "upperQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "levels" => refinementDataHistoryLevels stages packed T
local notation "image" => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace

theorem semanticStructuralPrefix_insertion_crossCollisions
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r row : R) (A largerA selections : ZFSet.{u}) (h : G) (D K V : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (selectionFunction : ZFSet.IsFunc A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections)
    (selected : selections ⊆ M.preparedWitnessSelections c.carrier T stages packed b.carrier
      (ZFSet.pair (c.encode r) A) A)
    (whole : relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections ∈ M.sets)
    (smallWhole : M.groundEmbeddable (relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections) ZFSet.omega)
    (below : row ≤ r) (belowH : row ≤ a.iso h r)
    (sourceSubset : A ⊆ largerA) (imageSubset : image (t.encode h) A ⊆ largerA)
    (fixed : h ∈ d.principalFix V) (cap : d.iso h D ≤ K)
    (anchorGood : ∀ idx u w E,
      stageOneAssignment idx u w ∈ A →
      ZFSet.pair idx E ∈ refinementIndexFieldGraph I b.carrier 2 →
      ZFSet.pair E (b.encode K) ∈ b.conditionOrder →
      ZFSet.pair E (b.encode V) ∈ b.conditionOrder)
    (profileGood : ∀ F ∈ M.preparedSelectionProfiles A stages upperQ b.carrier T selections,
      b.encode V ∉ F → b.encode K ∉ F) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    (∀ z ∈ image (t.encode h) A, ZFSet.pair z (b.encode (d.iso h D)) ∈
      stageOneDataBounds (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples) →
    ZFSet.pair (c.encode row) (assignmentCut levels alpha largerA) ∈ Q →
    stageOneRawCrossCollisions M fields A (image (t.encode h) A)
      (ZFSet.pair (c.encode row) (assignmentCut levels alpha largerA)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  dsimp only
  intro movedData validCut
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
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have profileFacts := M.preparedSelectionProfiles_ground_countable pairing unions powers separation collection
    infinite choice carrier hT hs hPacked nodes (run).carriers.data selected whole smallWhole
    (M.semanticStructuralTrace_storedPreparation_request_bounds c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace infinite choice)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let upper : SetMembers upperQ := SetMembers.ofMem _ source
  have upperCode : SetMembers.raw upper = ZFSet.pair (c.encode r) A := SetMembers.raw_ofMem _ _
  have actionCode (j : G) := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace j upper r A upperCode
  have sourceAct : ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A) ∈ upperQ :=
    actionCode h ▸ SetMembers.raw_mem ((upperAct).iso h upper)
  have imageOne : image (t.encode 1) A = A := by
    have equal := actionCode 1
    simp only [(upperAct).one, a.one, upperCode] at equal
    exact (ZFSet.pair_inj.1 equal).2.symm
  let qStrong : SetMembers Q := SetMembers.ofMem _ validCut
  have strongCode : lower.encode qStrong = ZFSet.pair (c.encode row)
      (assignmentCut levels alpha largerA) := SetMembers.raw_ofMem _ _
  intro sharedIdx hi rawU hu rawNewU hNewU rawW hw rawNewW hNewW original newMember
  have bound := movedData _ newMember
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ := M.exists_niceRefinementIndex_fields act lower b d
    alpha T T2 valid system.valid2 hi
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let x := stageOneAssignment idx rawU rawW
  let u : (M.nameDomain lower).names := ⟨⟨rawU, valid rawU hu⟩, M.transitive hT hu⟩
  let w : (M.nameDomain lower).names := ⟨⟨rawW, valid rawW hw⟩, M.transitive hT hw⟩
  let newU : (M.nameDomain lower).names := ⟨⟨rawNewU, valid rawNewU hNewU⟩, M.transitive hT hNewU⟩
  let newW : (M.nameDomain lower).names := ⟨⟨rawNewW, valid rawNewW hNewW⟩, M.transitive hT hNewW⟩
  obtain ⟨y, selectionEdge, _⟩ := selectionFunction.2 x original
  have valueBound := (ZFSet.pair_mem_prod.1 (selectionFunction.1 selectionEdge)).2
  obtain ⟨beta, _hBeta, output, ho, rfl⟩ := ZFSet.mem_prod.1 valueBound
  obtain ⟨sourceCondition, hSource, tail, ht, rfl⟩ := ZFSet.mem_prod.1 ho
  obtain ⟨sourceRow, _hSourceRow, sourceA, _hSourceA, rfl⟩ :=
    ZFSet.mem_prod.1 (M.refinementHistoryForcing_shape c.carrier T stages packed hSource)
  obtain ⟨k, _hkBound, enumerations, _heBound, rfl⟩ := ZFSet.mem_prod.1 ht
  obtain ⟨hBeta, sourceCondition, _sourceSubset, _hk, _he, other, otherStored,
      terms, _nodeCarrier, _meet, selectedAssignment, rawq, hq, cut, family⟩ :=
    M.preparedWitnessSelection_entry (run).carriers.data (selected selectionEdge)
  have inSource := (mem_assignmentOnIndices (other 0) T sourceA x).1 selectedAssignment
  have indexOther := (stageOneAssignment_mem_assignments (other 0) T idx rawU rawW).1 inSource.2
  have alphaEdge := (run).carriers.data.coverage alpha member fields canonicalStored idx hi rawU hu rawW hw
  have betaEdge := (run).carriers.data.coverage beta hBeta other otherStored idx indexOther.1
    rawU (terms.symm ▸ hu) rawW (terms.symm ▸ hw)
  have sameStage : beta = alpha := by
    have fn := (run).carriers.data.levels_function
    have hx := (ZFSet.pair_mem_prod.1 (fn.1 alphaEdge)).1
    obtain ⟨_, _, unique⟩ := fn.2 x hx
    exact (unique _ betaEdge).trans (unique _ alphaEdge).symm
  subst beta
  have sameFields : other = fields := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique otherStored canonicalStored)
  subst other
  obtain ⟨qOriginal, rfl⟩ := (lower.mem_carrier rawq).1 hq
  let cls := M.stageOneClassName lower pairing unions powers separation collection hQ orderGround hT valid
  have certificate (side : Fin 2) :
      ∃ F B f e names,
        ZFSet.pair ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain lower).names) side).val.val
          (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
        PreparedCertificateCode M lower.carrier lower.conditionOrder (lower.encode qOriginal)
          b.carrier b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder)
          (M.groundRelations T lower.carrier) (M.niceVisibilityGraph act lower b T d.principalFix)
          (lower.encode ⊤) ZFSet.omega
          ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain lower).names) side).val.val F B f e names := by
    have facts := M.semanticStructuralPrefix_assignmentClassRequest_mem c a t b d base directed
      T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
      group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
      symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice
      sourceCondition C E U Rf Rc hi u.val w.val hu hw inSource.1 side
    obtain ⟨F, B, f, e, names, _hF, _hB, _hf, _he, _hn, kEdge, _enumEdge, code⟩ :=
      selectedFamilyCertificate M family facts.1
    have nameEq : ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain lower).names) side).val.val =
        (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u.val (fun _ => w.val) side)).val := by
      exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) side
    exact ⟨F, B, f, e, names, nameEq.symm ▸ kEdge, nameEq.symm ▸ code⟩
  obtain ⟨F0, B0, f0, e0, names0, edge0, code0⟩ := certificate 0
  obtain ⟨F1, B1, f1, e1, names1, edge1, code1⟩ := certificate 1
  have profile0 := profileFacts.2.2.2 x alpha sourceRow sourceA k enumerations _ F0 B0 f0 selectionEdge edge0
  have profile1 := profileFacts.2.2.2 x alpha sourceRow sourceA k enumerations _ F1 B1 f1 selectionEdge edge1
  have testFacts := M.semanticStructuralPrefix_aligned_cut_tests_at_larger_cut c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
    r (a.iso h r) row A (image (t.encode h) A) largerA h 1 source sourceAct belowH le_rfl
    (by simpa only [a.one] using below) (fun _ hx => hx)
    (by simpa only [imageOne] using sourceSubset) imageSubset qOriginal qStrong cut strongCode
  have anchorEdge : ZFSet.pair idx (b.encode E) ∈ refinementIndexFieldGraph I b.carrier 2 := by
    obtain ⟨_, _, _, _, _, rawE, _, _, _, _, _, edge, _⟩ :=
      (stageOneDataBounds_assignment_entry (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples idx rawNewU rawNewW (b.encode (d.iso h D))).1 bound
    have same : rawE = b.encode E :=
      ((refinementIndexFieldGraph_entry I b.carrier ![alpha, b.encode C, b.encode E,
        U.val.val, Rf.val.val, Rc.val.val] 2 rawE).1 edge).2.2
    exact same ▸ edge
  have avoid : E ≤ K → E ≤ V := fun le =>
    (b.pair_mem_conditionOrder E V).1
      (anchorGood idx rawU rawW (b.encode E) original anchorEdge
        ((b.pair_mem_conditionOrder E K).2 le))
  have collisions := M.structuralAssignment_prepared_insertion_collision act lower t b d base directed
    alpha T T2 system pairing unions powers separation collection hQ orderGround group nodes supports hAlpha hT
    small trace.1 exactStored I S mu positions tuples A liftedSupport h D K V C E U Rf Rc u w newU newW
    hi hu hw hNewU hNewW qOriginal qStrong
    (by simpa only [(act).one] using testFacts.2.2.1) testFacts.2.2.2 fixed cap avoid
    ![F0, F1] ![B0, B1] ![f0, f1] ![e0, e1] ![names0, names1]
    (Fin.cases (profileGood F0 profile0)
      (Fin.cases (profileGood F1 profile1) (fun j => Fin.elim0 j)))
    original bound testFacts.1 testFacts.2.1
    (Fin.cases code0 (Fin.cases code1 (fun j => Fin.elim0 j)))
  rw [strongCode] at collisions
  exact collisions.2

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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
include hs hh ordinal trace
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "image" => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace

theorem semanticStructuralTrace_insertion_union
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r row : R) (A selections : ZFSet.{u}) (h : G) (D K V : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (selectionFunction : ZFSet.IsFunc A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections)
    (selected : selections ⊆ M.preparedWitnessSelections c.carrier T stages packed b.carrier
      (ZFSet.pair (c.encode r) A) A)
    (whole : relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections ∈ M.sets)
    (smallWhole : M.groundEmbeddable (relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections) ZFSet.omega)
    (below : row ≤ r) (belowH : row ≤ a.iso h r)
    (fixed : h ∈ d.principalFix V) (cap : d.iso h D ≤ K)
    (anchorGood : ∀ idx u w E,
      stageOneAssignment idx u w ∈ A →
      ZFSet.pair idx E ∈ refinementIndexFieldGraph I b.carrier 2 →
      ZFSet.pair E (b.encode K) ∈ b.conditionOrder →
      ZFSet.pair E (b.encode V) ∈ b.conditionOrder)
    (profileGood : ∀ F ∈ M.preparedSelectionProfiles A stages upperQ b.carrier T selections,
      b.encode V ∉ F → b.encode K ∉ F)
    (movedData : ∀ z ∈ image (t.encode h) A, ZFSet.pair z (b.encode (d.iso h D)) ∈
      stageOneDataBounds (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples) :
    ZFSet.pair (c.encode row) (A ∪ image (t.encode h) A) ∈ upperQ ∧
      ZFSet.pair (ZFSet.pair (c.encode row) (A ∪ image (t.encode h) A)) (ZFSet.pair (c.encode r) A) ∈
        M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
      ZFSet.pair (ZFSet.pair (c.encode row) (A ∪ image (t.encode h) A))
        (ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A)) ∈
        M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let upper : SetMembers upperQ := SetMembers.ofMem _ source
  have upperCode : SetMembers.raw upper = ZFSet.pair (c.encode r) A := SetMembers.raw_ofMem _ _
  have actionCode := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace h upper r A upperCode
  have sourceAct : ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A) ∈ upperQ :=
    actionCode ▸ SetMembers.raw_mem ((upperAct).iso h upper)
  apply M.semanticStructuralTrace_mixed_union_extension c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice
    (c.encode row) (c.encode r) (c.encode (a.iso h r)) A (image (t.encode h) A)
    source sourceAct ((c.pair_mem_conditionOrder row r).2 below)
    ((c.pair_mem_conditionOrder row (a.iso h r)).2 belowH)
  intro beta member fields stored validCut
  have canonical := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same := refinementFormulaDataCode_injective ((run).carriers.data.function.unique stored canonical)
  rw [same]
  exact M.semanticStructuralPrefix_insertion_crossCollisions c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice small I S mu positions tuples range support
    r row A (A ∪ image (t.encode h) A) selections h D K V source selectionFunction selected whole smallWhole
    below belowH (fun _ member => ZFSet.mem_union.2 (Or.inl member))
    (fun _ member => ZFSet.mem_union.2 (Or.inr member)) fixed cap anchorGood profileGood movedData validCut

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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
include hs hh ordinal trace
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "image" => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace

theorem semanticStructuralTrace_aligned_copy_union
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
    (meetGreatest : ∀ z : L, z ≤ d.iso h D → z ≤ X → z ≤ meet (d.iso h D) X)
    (newData : ∀ z ∈ image (t.encode h) A, ZFSet.pair z (b.encode (d.iso h D)) ∈
      stageOneDataBounds (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (oldData : ∀ z ∈ oldA, ZFSet.pair z (b.encode X) ∈
      stageOneDataBounds oldA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (descent : ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member ordinal member
      let subset := (And.left ordinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
      let lower := SetMembers.presentation Q
      let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : L) (x y : (M.nameDomain lower).names),
          d.principalFix v ≤ act.stabilizer lower x.val →
          d.principalFix w ≤ act.stabilizer lower y.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) x.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau.val ∧
            d.principalFix (meet v w) ≤ act.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) :
    ZFSet.pair (c.encode row) (image (t.encode h) A ∪ oldA) ∈ upperQ ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h) A ∪ oldA))
      (ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h) A ∪ oldA))
      (ZFSet.pair (c.encode oldRow) oldA) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let upperAct := M.semanticStructuralAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  let original : SetMembers upperQ := SetMembers.ofMem _ source
  have originalCode : SetMembers.raw original = ZFSet.pair (c.encode r) A := SetMembers.raw_ofMem _ _
  have movedCode := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace h original r A originalCode
  have movedSource : ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A) ∈ upperQ :=
    movedCode ▸ SetMembers.raw_mem (upperAct.iso h original)
  apply M.semanticStructuralTrace_mixed_union_extension c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice
    (c.encode row) (c.encode (a.iso h r)) (c.encode oldRow) (image (t.encode h) A) oldA
    movedSource oldSource ((c.pair_mem_conditionOrder _ _).2 belowH)
    ((c.pair_mem_conditionOrder _ _).2 belowOld)
  intro alpha member data stored validCut
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have canonicalStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same : data = fields := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique stored canonicalStored)
  subst data
  exact M.semanticStructuralPrefix_aligned_copy_crossCollisions c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice small meet I S mu positions tuples range support
    r oldRow row A oldA g h D X V source oldSource prepared belowOld oldBelowG belowH contains
    relative overlap meetLeft meetRight meetGreatest (descent alpha member) newData oldData validCut

end PartitionPilot.Forcing.TransitiveGround

end OAI
