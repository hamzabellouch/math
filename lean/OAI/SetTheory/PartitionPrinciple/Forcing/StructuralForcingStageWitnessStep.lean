import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStructuralForcingHistoryConstruction
import OAI.SetTheory.PartitionPrinciple.Forcing.StructuralAssignmentActionLaws
import OAI.SetTheory.PartitionPrinciple.Geometry.PresentedRowAssignmentTotality

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.PosetActionCode
open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (t : Presentation G) (s : Presentation P) {A : ZFSet.{u}}
variable (h : PosetActionCode t.carrier s.carrier
  ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1) s.conditionOrder A)

noncomputable def presentedAct (g : G) (p : P) : P :=
  (t.product s).decodeFunction s A h.function (g, p)

theorem presentedAct_entry (g : G) (p : P) :
    ZFSet.pair (ZFSet.pair (t.encode g) (s.encode p)) (s.encode (h.presentedAct t s g p)) ∈ A :=
  (t.product s).decodeFunction_mem s A h.function (g, p)

theorem presentedAct_eq_iff (g : G) (p q : P) :
    h.presentedAct t s g p = q ↔ ZFSet.pair (ZFSet.pair (t.encode g) (s.encode p)) (s.encode q) ∈ A :=
  (t.product s).decodeFunction_iff s A h.function (g, p) q

theorem presentedAct_one (p : P) : h.presentedAct t s 1 p = p :=
  (h.presentedAct_eq_iff t s 1 p p).2 (h.one _ (s.encode_mem p))

theorem presentedAct_mul (g j : G) (p : P) :
    h.presentedAct t s (g * j) p = h.presentedAct t s g (h.presentedAct t s j p) := by
  apply (h.presentedAct_eq_iff t s _ _ _).2
  exact h.mul _ (t.encode_mem g) _ (t.encode_mem j) _ (t.encode_mem (g * j))
    _ (s.encode_mem p) _ (s.encode_mem _) _ (s.encode_mem _)
    (((t.product t).pair_mem_graph t (fun gh => gh.1 * gh.2) (g, j) (g * j)).2 rfl)
    (h.presentedAct_entry t s j p) (h.presentedAct_entry t s g (h.presentedAct t s j p))

theorem presentedAct_inv_left (g : G) (p : P) :
    h.presentedAct t s g⁻¹ (h.presentedAct t s g p) = p := by
  rw [← h.presentedAct_mul t s, inv_mul_cancel, h.presentedAct_one t s]

theorem presentedAct_inv_right (g : G) (p : P) :
    h.presentedAct t s g (h.presentedAct t s g⁻¹ p) = p := by
  rw [← h.presentedAct_mul t s, mul_inv_cancel, h.presentedAct_one t s]

theorem presentedAct_monotone (g : G) : Monotone (h.presentedAct t s g) := by
  intro p q below
  apply (s.pair_mem_conditionOrder _ _).1
  exact h.monotone _ (t.encode_mem g) _ (s.encode_mem p) _ (s.encode_mem q)
    _ (s.encode_mem _) _ (s.encode_mem _) (h.presentedAct_entry t s g p)
    (h.presentedAct_entry t s g q) ((s.pair_mem_conditionOrder p q).2 below)

theorem presentedAct_le_iff (g : G) (p q : P) :
    h.presentedAct t s g p ≤ h.presentedAct t s g q ↔ p ≤ q := by
  constructor
  · intro below
    have back := h.presentedAct_monotone t s g⁻¹ below
    simpa only [h.presentedAct_inv_left t s] using back
  · exact fun below => h.presentedAct_monotone t s g below

noncomputable def toPresentedPosetAction : PosetAction G P where
  iso g := {
    toFun := h.presentedAct t s g
    invFun := h.presentedAct t s g⁻¹
    left_inv := h.presentedAct_inv_left t s g
    right_inv := h.presentedAct_inv_right t s g
    map_rel_iff' := h.presentedAct_le_iff t s g _ _ }
  one := h.presentedAct_one t s
  mul := h.presentedAct_mul t s

theorem toPresentedPosetAction_graph : (h.toPresentedPosetAction t s).actionGraph s t = A :=
  (t.product s).graph_decodeFunction s A h.function

end PartitionPilot.Forcing.PosetActionCode



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (Q J B : ZFSet.{u})

theorem presentedRowAssignmentGraph_code
    (shape : Q ⊆ ZFSet.prod c.carrier (ZFSet.powerset J))
    (laws : RelationActionLaws G J (fun g => rawActionSection (t.encode g) B J))
    (preserves : ∀ g : G, ∀ r : R, ∀ A,
      ZFSet.pair (c.encode r) A ∈ Q →
      ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)) ∈ Q) :
    PosetActionCode t.carrier Q ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
      (rawRowAssignmentOrder Q c.conditionOrder)
      (rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B) := by
  refine ⟨presentedRowAssignmentGraph_function a c t Q J B shape preserves, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨r, A, hA, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hp
    exact (presentedRowAssignmentGraph_entry a c t Q J B 1 r r A A).2
      ⟨hp, hp, a.one r, (laws.image_one (ZFSet.mem_powerset.1 hA)).symm⟩
  · intro g hg h hh k hk p hp q hq r hr product first second
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨h, rfl⟩ := (t.mem_carrier h).1 hh
    obtain ⟨k, rfl⟩ := (t.mem_carrier k).1 hk
    have gh := ((t.product t).pair_mem_graph t (fun gh => gh.1 * gh.2) (g, h) k).1 product
    obtain ⟨rp, A, hA, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hp
    obtain ⟨rq, D, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hq
    obtain ⟨rr, E, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hr
    obtain ⟨_, _, firstRow, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B h rp rq A D).1 first
    obtain ⟨_, _, secondRow, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g rq rr _ E).1 second
    apply (presentedRowAssignmentGraph_entry a c t Q J B k rp rr A _).2
    refine ⟨hp, hr, ?_, ?_⟩
    · rw [← gh, a.mul, firstRow, secondRow]
    · rw [← gh]
      exact (laws.image_mul g h (ZFSet.mem_powerset.1 hA)).symm
  · intro g hg p hp q hq r hr s hs first second below
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨rp, A, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hp
    obtain ⟨rq, D, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hq
    obtain ⟨rr, E, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hr
    obtain ⟨rs, F, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hs
    obtain ⟨_, _, firstRow, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g rp rr A E).1 first
    obtain ⟨_, _, secondRow, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g rq rs D F).1 second
    obtain ⟨_, _, rows, assignments⟩ := (pair_mem_rawRowAssignmentOrder _ _ _ _ _ _).1 below
    apply (pair_mem_rawRowAssignmentOrder _ _ _ _ _ _).2
    refine ⟨hr, hs, ?_, ?_⟩
    · apply (c.pair_mem_conditionOrder rr rs).2
      rw [← firstRow, ← secondRow]
      exact (a.iso g).monotone ((c.pair_mem_conditionOrder rp rq).1 rows)
    · intro y hy
      obtain ⟨hy, x, hx, edge⟩ := (mem_relationImage _ J _ y).1 hy
      exact (mem_relationImage _ J _ y).2 ⟨hy, x, assignments hx, edge⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem structuralForcingCarrier_shape
    (rows G nodes nodeOrder basis T T2 stages history : ZFSet.{u}) :
    M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history ⊆
      ZFSet.prod rows (ZFSet.powerset
        (M.structuralAssignments G nodes nodeOrder basis T T2 stages history)) := by
  intro z member
  have candidate := (M.mem_refinementHistoryForcing rows T stages
    (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) z).1 member |>.1
  obtain ⟨row, hrow, A, _hA, subset, _small, rfl⟩ := (M.mem_stageOneCandidateBound _ _ _ _).1 candidate
  exact ZFSet.pair_mem_prod.2 ⟨hrow, ZFSet.mem_powerset.2 subset⟩

theorem structuralForcingCarrier_action_candidate
    {G R : Type u} [Group G] [PartialOrder R]
    (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
    (nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hG : t.carrier ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hna : nodeAction ∈ M.sets) (hb : basis ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets)
    (laws : RelationActionLaws G
      (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)
      (fun g => rawActionSection (t.encode g)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)))
    (g : G) (row : R) (A : ZFSet.{u})
    (member : ZFSet.pair (c.encode row) A ∈
      M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history) :
    ZFSet.pair (c.encode (a.iso g row))
      (M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A) ∈
      M.stageOneCandidateBound c.carrier
        (refinementDataHistoryIndices stages
          (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)) T := by
  have candidate := (M.mem_refinementHistoryForcing c.carrier T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
      (ZFSet.pair (c.encode row) A)).1 member |>.1
  have small := (ZFSet.pair_mem_prod.1 candidate).2
  exact ZFSet.pair_mem_prod.2 ⟨c.encode_mem (a.iso g row),
    M.structuralAssignmentImage_small pairing unions powers separation collection
      hG hn hno hna hb hT hT2 hs hh omega (M.transitive hG (t.encode_mem g))
      (laws.injection g) small⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u})
variable (laws : RelationActionLaws G
  (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)
  (fun g => rawActionSection (t.encode g)
    (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)
    (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)))
variable (preserves : ∀ g : G, ∀ r : R, ∀ A,
  ZFSet.pair (c.encode r) A ∈ M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history →
  ZFSet.pair (c.encode (a.iso g r))
    (M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A) ∈
    M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history)

noncomputable def structuralForcingAction :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
    PosetAction G (SetMembers (M.refinementHistoryForcing c.carrier T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history))) := by
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  let Q := M.refinementHistoryForcing c.carrier T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  have code : PosetActionCode t.carrier Q ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
      (SetMembers.presentation Q).conditionOrder
      (rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history) (a.actionGraph c t)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)) := by
    rw [M.refinementHistoryDecodedOrder_eq, M.refinementHistoryOrder_raw]
    exact presentedRowAssignmentGraph_code a c t Q _ _
      (M.structuralForcingCarrier_shape c.carrier t.carrier nodes nodeOrder basis T T2 stages history) laws preserves
  exact code.toPresentedPosetAction t (SetMembers.presentation Q)

theorem structuralForcingAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
    (M.structuralForcingAction a c t nodes nodeOrder nodeAction basis T T2 stages history laws preserves).actionGraph
      (SetMembers.presentation (M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history)) t =
      rawRowAssignmentActionGraph t.carrier
        (M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history) c.carrier
        (⋃₀ ⋃₀ (M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history))
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history) (a.actionGraph c t)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  unfold structuralForcingAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem structuralForcingAction_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
    ∀ g (p : SetMembers (M.refinementHistoryForcing c.carrier T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history))) r A,
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((M.structuralForcingAction a c t nodes nodeOrder nodeAction basis T T2 stages history laws preserves).iso g p) =
        ZFSet.pair (c.encode (a.iso g r))
          (M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  intro g p r A equal
  let Q := M.refinementHistoryForcing c.carrier T stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history)
  let act := M.structuralForcingAction a c t nodes nodeOrder nodeAction basis T T2 stages history laws preserves
  have edge := (act.triple_mem_actionGraph (SetMembers.presentation Q) t g p (act.iso g p)).2 rfl
  have graph := M.structuralForcingAction_graph a c t nodes nodeOrder nodeAction basis T T2 stages history laws preserves
  change act.actionGraph (SetMembers.presentation Q) t = _ at graph
  rw [graph] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw (act.iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c
    (M.structuralForcingCarrier_shape c.carrier t.carrier nodes nodeOrder basis T T2 stages history) (SetMembers.raw_mem (act.iso g p))
  rw [equal, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q _ _ g r q A D).1 edge
  rw [target, row, data]
  rfl

omit [Group G] in
theorem structuralAssignmentImage_empty (g : ZFSet.{u}) :
    M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history g ∅ = ∅ := by
  apply ZFSet.ext
  intro y
  constructor
  · intro member
    obtain ⟨_, x, hx, _⟩ := (mem_relationImage _ _ _ y).1 member
    exact False.elim (ZFSet.notMem_empty x hx)
  · intro member
    exact False.elim (ZFSet.notMem_empty y member)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (rowTop nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralTrace_cutAction {stages history level P order top action : ZFSet.{u}}
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun beta prior stage =>
      stage = M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier nodes nodeOrder nodeAction basis T T2 beta prior) stages history)
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history)
    (function : ZFSet.IsFunc (ZFSet.prod t.carrier P) P action)
    (g : G) (r : R) (A : ZFSet.{u})
    (lower : ZFSet.pair (c.encode r)
      (assignmentCut (refinementDataHistoryLevels stages
        (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history) T) level A) ∈ P) :
    let levels := refinementDataHistoryLevels stages
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history) T
    let moved := M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A
    let nextLower := ZFSet.pair (c.encode (a.iso g r)) (assignmentCut levels level moved)
    nextLower ∈ P ∧
      ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode r) (assignmentCut levels level A))) nextLower ∈ action := by
  dsimp only
  have hl := trace.1.pair_source stored
  have code := (trace.2 level hl _ stored).trans
    (M.structuralForcingStage_eq c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier nodes nodeOrder nodeAction basis T T2 level (graphRestriction level history))
  obtain ⟨carrierEq, _orderEq, _topEq, actionEq⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 code
  rw [carrierEq, actionEq] at function
  have lowerMember := carrierEq ▸ lower
  have result := presentedRowAssignmentGraph_totalValue a c t
    (M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 level (graphRestriction level history))
    (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 level (graphRestriction level history))
    (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 level (graphRestriction level history))
    (M.refinementHistoryForcing_shape c.carrier T level
      (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 level (graphRestriction level history)))
    function g r _ lowerMember
  rw [carrierEq, actionEq]
  rw [M.structuralAssignmentImage_prefix_cut t.carrier nodes nodeOrder nodeAction basis T T2
    trace.1 (ordinal.1 level hl)]
  exact result

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (rowTop nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralForcingCarrier_action_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hG : t.carrier ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hna : nodeAction ∈ M.sets) (hb : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun beta prior stage =>
      stage = M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier nodes nodeOrder nodeAction basis T T2 beta prior) stages history)
    (laws : RelationActionLaws G
      (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)
      (fun g => rawActionSection (t.encode g)
        (M.structuralAssignmentActionGraph t.carrier nodes nodeOrder nodeAction basis T T2 stages history)
        (M.structuralAssignments t.carrier nodes nodeOrder basis T T2 stages history)))
    (functions : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
        ZFSet.IsFunc (ZFSet.prod t.carrier P) P action)
    (symmetry : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      ∀ (g : G) (A p q : ZFSet.{u}), ZFSet.pair (ZFSet.pair (t.encode g) p) q ∈ action →
        (stageOneRawTests M (M.rawRefinementFormulaData P order top action t.carrier nodes nodeOrder basis T T2 level)
          (relationImage A
            (stageOneAssignments (M.rawRefinementFormulaData P order top action t.carrier nodes nodeOrder basis T T2 level 0) T)
            (M.rawStageRefinementAssignmentActionGraph (t.encode g) P order top action t.carrier
              nodes nodeOrder nodeAction basis T T2 level)) q ↔
        stageOneRawTests M (M.rawRefinementFormulaData P order top action t.carrier nodes nodeOrder basis T T2 level) A p))
    (g : G) (row : R) (A : ZFSet.{u})
    (member : ZFSet.pair (c.encode row) A ∈
      M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history) :
    ZFSet.pair (c.encode (a.iso g row))
      (M.structuralAssignmentImage t.carrier nodes nodeOrder nodeAction basis T T2 stages history (t.encode g) A) ∈
      M.structuralForcingCarrier c.carrier t.carrier nodes nodeOrder basis T T2 stages history := by
  have candidate := M.structuralForcingCarrier_action_candidate a c t nodes nodeOrder nodeAction basis T T2
    stages history pairing unions powers separation collection hG hn hno hna hb hT hT2 hs hh omega laws g row A member
  have previous := (M.mem_refinementHistoryForcing c.carrier T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history) _).1 member |>.2
  apply (M.mem_refinementHistoryForcing c.carrier T stages
    (M.structuralRefinementHistory t.carrier nodes nodeOrder basis T T2 stages history) _).2
  refine ⟨candidate, ?_⟩
  intro level hl
  obtain ⟨packet, entry, valid⟩ := previous level hl
  obtain ⟨data, rfl⟩ := M.structuralRefinementHistory_decoded t.carrier nodes nodeOrder basis T T2 stages history entry
  obtain ⟨_, P, order, top, action, stored, rfl⟩ :=
    M.structuralRefinementHistory_fields t.carrier nodes nodeOrder basis T T2 stages history data entry
  refine ⟨_, entry, ?_⟩
  rw [packedSuccessorConditionCode_code_iff, stageTwoConditionCode_pair_iff] at valid ⊢
  obtain ⟨lower, tests⟩ := valid
  have moved := M.structuralTrace_cutAction a c t rowTop nodes nodeOrder nodeAction basis T T2
    ordinal trace stored (functions level P order top action stored) g row A lower
  refine ⟨moved.1, ?_⟩
  apply (M.structuralAssignmentImage_rawTests_branch_iff t.carrier nodes nodeOrder nodeAction basis T T2
    trace.1 (t.encode_mem g) stored A _).2
  exact (symmetry level P order top action stored g A _ _ moved.2).2 tests

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

theorem structuralForcingStage_witness_step
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (earlier : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      RawRefinementStageWitness M t b d base directed T T2 level P order top action)
    (P order top action : ZFSet.{u})
    (output : forcingStageCode P order top action =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history) :
    RawRefinementStageWitness M t b d base directed T T2 stages P order top action := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  have hPacked : packed ∈ M.sets :=
    M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  have fields : ∀ level P order top action,
      ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      ∀ j, (![level, P, order, top, action] : Fin 5 → ZFSet.{u}) j ∈ M.sets := by
    intro level P order top action stored
    exact M.nonemptyTupleCode_field_mem 4 ![level, P, order, top, action] (M.transitive hh stored)
  have laws := M.structuralAssignment_relationLaws t b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history trace.1 (by
      intro level _hl P order top action stored
      have ground := fields level P order top action stored
      exact (earlier level P order top action stored).relationLaws pairing unions powers separation collection
        (ground 1) group nodes (ground 2) supports (ground 0) hT)
  have preserves := M.structuralForcingCarrier_action_mem a c t rowTop b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
    pairing unions powers separation collection group nodes nodeOrder nodeAction supports hT hT2 hs hh omega
    ordinal trace laws (fun level P order top action stored =>
      (earlier level P order top action stored).action_function) (by
      intro level P order top action stored g A p q edge
      have ground := fields level P order top action stored
      exact (earlier level P order top action stored).rawTests_actionGraph_iff
        pairing unions powers separation collection (ground 1) group nodes (ground 2) supports (ground 0) hT g A p q edge)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed run.carriers ordinal carrier rowTop topMem topRows
  let e := M.structuralForcingAction a c t b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history laws preserves
  have graph := M.structuralForcingAction_graph a c t b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history laws preserves
  have actionGround : e.actionGraph (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)) t ∈ M.sets := by
    change e.actionGraph (SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)) t = _ at graph
    rw [graph]
    exact M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hs hh omega
  have system := M.recursiveRefinementStageSystem c a t b d base directed T T2 stages packed run.carriers ordinal
    pairing unions powers separation collection carrier rowOrderGround group nodes nodeOrder nodeMaps supports hT hT2 hs hPacked omega
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 rowTop topMem topRows e
    (fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A)
    (M.structuralForcingAction_coordinates a c t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history laws preserves)
    (fun g => M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g)) actionGround
  have equal := output.trans (M.structuralForcingStage_eq c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 equal
  exact ⟨M.refinementHistoryOrder_partialOrder c.conditionOrder_code T stages packed,
    run.carriers.empty_assignments ordinal carrier topMem,
    run.carriers.greatest ordinal carrier topMem topRows, e, graph, system⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
