import OAI.SetTheory.PartitionPrinciple.Definability.GroundLiftedRowTupleSupports
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralDataSupport

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

variable {stages history alpha : ZFSet.{u}} (hh : history ∈ M.sets)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
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
include hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_code :
    PosetActionCode t.carrier Q ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
      (M.refinementHistoryOrder c.carrier c.conditionOrder T alpha lowerPacked) rawGraph := by
  have code := M.semanticStructuralAction_code c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hAlpha
    (M.graphRestriction_mem unions separation hAlpha hh) cutOrdinal (trace.restrict cutOrdinal subset)
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  rw [packedEq, M.structuralAssignments_history_restrict, M.structuralAssignmentActionGraph_history_restrict] at code
  exact code

noncomputable def semanticStructuralPrefixAction :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    PosetAction G (SetMembers Q) := by
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  have code := M.semanticStructuralPrefixAction_code c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  rw [← M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T alpha lowerPacked] at code
  exact code.toPresentedPosetAction t (SetMembers.presentation Q)

local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    (act).actionGraph (SetMembers.presentation Q) t = rawGraph := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  unfold semanticStructuralPrefixAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem semanticStructuralPrefixAction_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    ∀ (g : G) (p : SetMembers Q) (r : R) (A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((act).iso g p) = ZFSet.pair (c.encode (a.iso g r))
        (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  intro g p r A code
  have edge := ((act).triple_mem_actionGraph (SetMembers.presentation Q) t g p ((act).iso g p)).2 rfl
  rw [M.semanticStructuralPrefixAction_graph] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw ((act).iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier T alpha lowerPacked) (SetMembers.raw_mem ((act).iso g p))
  rw [code, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q _ _ g r q A D).1 edge
  rw [target, row, data]
  rfl

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem binaryRowSemanticPrefixTuple_supported {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (muOrdinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
    ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
      (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (stagesOrdinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared stages history
    ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
    let hAlpha := M.transitive hs member
    let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
    let subset := (And.left stagesOrdinal) alpha member
    let Q := M.refinementHistoryForcing c.carrier lifted alpha (graphRestriction alpha packed)
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha (graphRestriction alpha packed)
    let lower := SetMembers.presentation Q
    let actual := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hh trace hAlpha cutOrdinal subset
    ∀ (D : L) (f : ZFSet.{u}), f ∈ S →
      ∀ tau : Name lower, ZFSet.pair f tau.val ∈ tuples →
        RowPositionBound mu s.nonbottom.carrier s.conditionOrder f (s.encode D) →
        a.principalFix D ≤ actual.stabilizer lower tau := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace coordinates two carrier forcingOrder
    forcingAction omega topMem topRows packed alpha member hAlpha cutOrdinal subset Q
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha (graphRestriction alpha packed)
  intro lower actual D
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let restricted := run.carriers.restrict cutOrdinal subset
  let image := fun g A => M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder
    (a.actionGraph s b) (supportBasisCode s b a.principalFix) lifted squared alpha history (b.encode g) A
  have actionCoordinates := M.semanticStructuralPrefixAction_coordinates c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder
    forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1
    closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty b s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared alpha history (b.encode g)
  exact act.positionSupport_of_codeLift c.pairEmpty actual lower
    (M.refinementHistoryRowNameLift c restricted cutOrdinal carrier)
    (M.refinementHistoryRowNameLift_val c restricted cutOrdinal carrier)
    (M.refinementHistoryRowNameLift_stabilizer c restricted cutOrdinal carrier
      act actual image actionCoordinates emptyImage)
    lifted valid1 s a S mu s.nonbottom.carrier tuples D
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun f _ tau entry bound => M.liftedRowTuple_supported a s b C pairing unions powers separation
      infinite hL hC hG graph hmu muOrdinal valid f tau D entry bound.2)

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

theorem semanticStructuralRestriction_equivariant :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (g : G) (p : SetMembers Q), pi ((upperAct).iso g p) = (lowerAct).iso g (pi p) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro g p
  obtain ⟨r, A, _, code⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier T stages packed) (SetMembers.raw_mem p)
  have moved := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace g p r A code
  have cutCode := (run).restrictionFunction_raw ordinal cutOrdinal subset p (c.encode r) A code
  apply SetMembers.raw_injective LQ
  rw [(run).restrictionFunction_raw ordinal cutOrdinal subset ((upperAct).iso g p)
    (c.encode (a.iso g r)) _ moved,
    M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      g (pi p) r (assignmentCut levels alpha A) cutCode]
  exact congrArg (ZFSet.pair (c.encode (a.iso g r)))
    (M.structuralAssignmentImage_cut t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 trace.1 subset (t.encode g) A)

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

theorem semanticStructuralInclusion_equivariant :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (g : G) (p : SetMembers LQ), (upperAct).iso g (inc p) = inc ((lowerAct).iso g p) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro g p
  obtain ⟨r, A, _, code⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier T alpha (graphRestriction alpha packed)) (SetMembers.raw_mem p)
  have includeCode := (run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation
    infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono
  have member := code ▸ SetMembers.raw_mem p
  have data := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1
    ((M.mem_refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed) _).1 member).1).2.2.1
  have fixedCut := (run).carriers.data.prefix_assignments_cut subset data
  have equalImage := M.structuralAssignmentImage_domain_restrict t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 trace.1 subset (t.encode g) A
  rw [← M.structuralAssignments_cut_eq t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 subset, fixedCut] at equalImage
  apply SetMembers.raw_injective Q
  rw [M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace g (inc p) r A
      ((includeCode p).trans code),
    includeCode ((lowerAct).iso g p),
    M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset g p r A code]
  exact congrArg (ZFSet.pair (c.encode (a.iso g r))) equalImage.symm

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
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
include hs hh ordinal trace

theorem semanticStructuralPower_family (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let X := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    ∃ _valid : ∀ z ∈ X, IsName (SetMembers.presentation Q) z,
      X ∈ M.sets ∧
      (∀ g (tau : Name (SetMembers.presentation Q)), tau.val ∈ X →
        ((upperAct).act (SetMembers.presentation Q) g tau).val ∈ X) ∧
      (∀ tau : Name (SetMembers.presentation Q), tau.val ∈ X →
        HereditarilySymmetric upperAct (SetMembers.presentation Q)
          (d.principalSupportFamily base directed) tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A
  have coordinates := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g)
  obtain ⟨valid, closed, symmetric⟩ := M.refinementHistoryRowNameFamily_transport c
    (run).carriers ordinal carrier a upperAct image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  have topEq := M.refinementHistoryDecodedTop_eq c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  have validPower := iteratedPairNameFamily_valid ⊤ valid n
  have closedPower := iteratedPairNameFamily_closed upperAct valid closed n
  have symmetricPower := iteratedPairNameFamily_hs upperAct
    (d.principalSupportFamily base directed) valid symmetric n
  rw [topEq] at validPower closedPower symmetricPower
  exact ⟨validPower, M.iteratedPairNameFamily_mem pairing unions powers separation
    (M.orderedPair_mem pairing (M.transitive carrier topMem) (M.empty_mem ⟨T, hT⟩)) hT n,
    closedPower, symmetricPower⟩

variable {alpha : ZFSet.{u}} (hAlpha : alpha ∈ M.sets)
variable (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hAlpha cutOrdinal subset

omit hs in
theorem semanticStructuralPrefixPower_family (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    let X := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    ∃ _valid : ∀ z ∈ X, IsName (SetMembers.presentation LQ) z,
      X ∈ M.sets ∧
      (∀ g (tau : Name (SetMembers.presentation LQ)), tau.val ∈ X →
        ((lowerAct).act (SetMembers.presentation LQ) g tau).val ∈ X) ∧
      (∀ tau : Name (SetMembers.presentation LQ), tau.val ∈ X →
        HereditarilySymmetric lowerAct (SetMembers.presentation LQ)
          (d.principalSupportFamily base directed) tau) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨valid, closed, symmetric⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a lowerAct image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  have topEq := M.refinementHistoryDecodedTop_eq c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  have validPower := iteratedPairNameFamily_valid ⊤ valid n
  have closedPower := iteratedPairNameFamily_closed lowerAct valid closed n
  have symmetricPower := iteratedPairNameFamily_hs lowerAct
    (d.principalSupportFamily base directed) valid symmetric n
  rw [topEq] at validPower closedPower symmetricPower
  exact ⟨validPower, M.iteratedPairNameFamily_mem pairing unions powers separation
    (M.orderedPair_mem pairing (M.transitive carrier topMem) (M.empty_mem ⟨T, hT⟩)) hT n,
    closedPower, symmetricPower⟩

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

theorem semanticStructuralCutGraph_act :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    ∀ (g : G) (p : SetMembers Q) (q : ZFSet.{u}) (hq : q ∈ LQ),
      ZFSet.pair (SetMembers.raw p) q ∈ rowAssignmentCutGraph Q LQ levels alpha →
      q = SetMembers.raw (pi p) ∧
      ZFSet.pair (SetMembers.raw ((upperAct).iso g p))
        (SetMembers.raw ((lowerAct).iso g (SetMembers.ofMem q hq))) ∈
        rowAssignmentCutGraph Q LQ levels alpha := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  intro g p q hq selected
  let lower := SetMembers.ofMem q hq
  have graph := (run).restrictionFunction_graph ordinal cutOrdinal subset
  have decoded : pi p = lower := by
    apply ((SetMembers.presentation Q).pair_mem_graph (SetMembers.presentation LQ) pi p lower).1
    rw [graph]
    change ZFSet.pair (SetMembers.raw p) (SetMembers.raw lower) ∈ _
    simpa only [lower, SetMembers.raw_ofMem] using selected
  have exactTarget : q = SetMembers.raw (pi p) := by
    rw [decoded]
    exact (SetMembers.raw_ofMem q hq).symm
  refine ⟨exactTarget, ?_⟩
  rw [← graph]
  change ZFSet.pair ((SetMembers.presentation Q).encode ((upperAct).iso g p))
    ((SetMembers.presentation LQ).encode ((lowerAct).iso g lower)) ∈ _
  apply ((SetMembers.presentation Q).pair_mem_graph (SetMembers.presentation LQ) pi
    ((upperAct).iso g p) ((lowerAct).iso g lower)).2
  have equivariant := M.semanticStructuralRestriction_equivariant c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
    nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows
    hs hh ordinal trace hAlpha cutOrdinal subset g p
  exact equivariant.trans (congrArg ((lowerAct).iso g) decoded)

end PartitionPilot.Forcing.TransitiveGround

end OAI
