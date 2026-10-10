import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAlignedCopyUnions

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

local notation "upperQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "levels" => refinementDataHistoryLevels stages packed T
local notation "image" => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace

theorem semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r oldRow row : R) (A oldA largerA : ZFSet.{u}) (g h : G) (D X V : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair (c.encode r) A))
    (belowOld : row ≤ oldRow) (oldBelowG : oldRow ≤ a.iso g r) (belowH : row ≤ a.iso h r)
    (contains : image (t.encode g) A ⊆ oldA)
    (movedSubset : image (t.encode h) A ⊆ largerA)
    (oldSubset : oldA ⊆ largerA)
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
      ZFSet.pair (c.encode row) (assignmentCut levels alpha largerA) ∈ Q →
      stageOneRawCrossCollisions M fields (image (t.encode h) A) oldA
        (ZFSet.pair (c.encode row) (assignmentCut levels alpha largerA)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
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
      (assignmentCut levels alpha largerA) := SetMembers.raw_ofMem _ _
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
  have testFacts := M.semanticStructuralPrefix_aligned_cut_tests_at_larger_cut c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member r oldRow row A oldA largerA g h source oldSource
    belowOld oldBelowG belowH contains movedSubset oldSubset qOriginal qStrong cut strongCode
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

theorem semanticStructuralTrace_aligned_rectangle_union
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r oldRow row : R) (A oldA : ZFSet.{u}) (g1 g2 h1 h2 : G) (D X V W : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair (c.encode r) A))
    (belowOld : row ≤ oldRow)
    (oldBelowG1 : oldRow ≤ a.iso g1 r) (oldBelowG2 : oldRow ≤ a.iso g2 r)
    (belowH1 : row ≤ a.iso h1 r) (belowH2 : row ≤ a.iso h2 r)
    (contains1 : image (t.encode g1) A ⊆ oldA)
    (contains2 : image (t.encode g2) A ⊆ oldA)
    (relative1 : g1⁻¹ * h1 ∈ d.principalFix V)
    (relative2 : g2⁻¹ * h2 ∈ d.principalFix V)
    (between : h1⁻¹ * h2 ∈ d.principalFix W)
    (overlap1 : meet (d.iso h1 D) X = d.iso h1 V)
    (overlap2 : meet (d.iso h2 D) X = d.iso h2 V)
    (overlap12 : meet (d.iso h1 D) (d.iso h2 D) = d.iso h1 W)
    (meetComm : ∀ x y : L, meet x y = meet y x)
    (meetLeft : ∀ x y : L, meet x y ≤ x)
    (meetRight : ∀ x y : L, meet x y ≤ y)
    (meetGreatest : ∀ x y z : L, z ≤ x → z ≤ y → z ≤ meet x y)
    (data1 : ∀ z ∈ image (t.encode h1) A, ZFSet.pair z (b.encode (d.iso h1 D)) ∈
      stageOneDataBounds (image (t.encode h1) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (data2 : ∀ z ∈ image (t.encode h2) A, ZFSet.pair z (b.encode (d.iso h2 D)) ∈
      stageOneDataBounds (image (t.encode h2) A) I T S b.carrier mu positions b.conditionOrder
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
    ZFSet.pair (c.encode row) (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)) ∈ upperQ ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)))
      (ZFSet.pair (c.encode oldRow) oldA) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)))
      (ZFSet.pair (c.encode (a.iso h1 r)) (image (t.encode h1) A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)))
      (ZFSet.pair (c.encode (a.iso h2 r)) (image (t.encode h2) A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let upperAct := M.semanticStructuralAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  let original : SetMembers upperQ := SetMembers.ofMem _ source
  have originalCode : SetMembers.raw original = ZFSet.pair (c.encode r) A := SetMembers.raw_ofMem _ _
  have movedSource (j : G) : ZFSet.pair (c.encode (a.iso j r)) (image (t.encode j) A) ∈ upperQ := by
    have movedCode := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace j original r A originalCode
    exact movedCode ▸ SetMembers.raw_mem (upperAct.iso j original)
  have first := M.semanticStructuralTrace_aligned_copy_union c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
    infinite choice small meet I S mu positions tuples range support
    r oldRow row A oldA g1 h1 D X V source oldSource prepared belowOld oldBelowG1 belowH1 contains1
    relative1 overlap1 (meetLeft _ _) (meetRight _ _) (meetGreatest _ _) data1 oldData descent
  have sameW : d.iso h2 W = d.iso h1 W := by
    have equal := congrArg (d.iso h1) (between W le_rfl)
    rw [d.mul, d.point_inv_right] at equal
    exact equal
  have overlap21 : meet (d.iso h2 D) (d.iso h1 D) = d.iso h2 W :=
    (meetComm _ _).trans (overlap12.trans sameW.symm)
  have full : ZFSet.pair (c.encode row)
      (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)) ∈ upperQ := by
    refine (M.semanticStructuralTrace_mixed_union_extension c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace infinite choice
      (c.encode row) (c.encode (a.iso h2 r)) (c.encode row)
      (image (t.encode h2) A) (image (t.encode h1) A ∪ oldA)
      (movedSource h2) first.1 ((c.pair_mem_conditionOrder _ _).2 belowH2)
      ((c.pair_mem_conditionOrder _ _).2 le_rfl) ?_).1
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
    have againstOld := M.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
      infinite choice small meet I S mu positions tuples range support
      r oldRow row A oldA (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)) g2 h2 D X V
      source oldSource prepared belowOld oldBelowG2 belowH2 contains2
      (fun _ hz => ZFSet.mem_union.2 (Or.inl hz))
      (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr hz))))
      relative2 overlap2 (meetLeft _ _) (meetRight _ _) (meetGreatest _ _) (descent alpha member)
      data2 oldData validCut
    have againstFirst := M.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
      infinite choice small meet I S mu positions tuples range support
      r (a.iso h1 r) row A (image (t.encode h1) A)
      (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)) h1 h2 D (d.iso h1 D) W
      source (movedSource h1) prepared belowH1 le_rfl belowH2 (fun _ hz => hz)
      (fun _ hz => ZFSet.mem_union.2 (Or.inl hz))
      (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz))))
      between overlap21 (meetLeft _ _) (meetRight _ _) (meetGreatest _ _) (descent alpha member)
      data2 data1 validCut
    intro idx hi u hu u' hu' w hw w' hw' newMember oldMember
    rcases ZFSet.mem_union.1 oldMember with inFirst | inOld
    · exact againstFirst idx hi u hu u' hu' w hw w' hw' newMember inFirst
    · exact againstOld idx hi u hu u' hu' w hw w' hw' newMember inOld
  refine ⟨full, ?_, ?_, ?_⟩
  · exact (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed _ _ _ _).2
      ⟨full, oldSource, (c.pair_mem_conditionOrder _ _).2 belowOld,
        fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr hz)))⟩
  · exact (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed _ _ _ _).2
      ⟨full, movedSource h1, (c.pair_mem_conditionOrder _ _).2 belowH1,
        fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz)))⟩
  · exact (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed _ _ _ _).2
      ⟨full, movedSource h2, (c.pair_mem_conditionOrder _ _).2 belowH2,
        fun _ hz => ZFSet.mem_union.2 (Or.inl hz)⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
