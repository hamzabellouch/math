import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStructuralForcingActionGraphs
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundRecursiveRowCompleteProjection
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSmallAssignmentCuts
import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveStructuralRefinementHistories

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem small_refinementConditionFamily_prefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows T K history D : ZFSet.{u}} (hRows : rows ∈ M.sets) (hT : T ∈ M.sets)
    (hK : K ∈ M.sets) (hHistory : history ∈ M.sets) (hD : D ∈ M.sets)
    (ordinal : ordinalSetProperty K) (omega : ZFSet.omega ∈ K)
    (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (run : RecursiveRefinementDataHistory M rows T K history)
    (small : GroundBelow M D K) (members : D ⊆ M.refinementHistoryForcing rows T K history) :
    ∃ beta ∈ K, ∀ row A, ZFSet.pair row A ∈ D →
      assignmentCut (refinementDataHistoryLevels K history T) beta A = A ∧
      ZFSet.pair row A ∈ M.refinementHistoryForcing rows T beta (graphRestriction beta history) := by
  let J := stageOneAssignments (refinementDataHistoryIndices K history) T
  let S := M.groundSmallSubsets J ZFSet.omega
  let projection := productSecond rows S
  let R := relationImage D S projection
  let U := ⋃₀ R
  have hJ : J ∈ M.sets := M.stageOneAssignments_mem pairing unions powers separation
    (M.refinementDataHistoryIndices_mem pairing unions powers separation hK hHistory) hT
  have hS : S ∈ M.sets := M.groundSmallSubsets_mem powers separation hJ (M.transitive hK omega)
  have hProjection : projection ∈ M.sets := M.productSecond_mem pairing unions powers separation hRows hS
  have hR : R ∈ M.sets := M.relationImage_mem separation hD hS hProjection
  have hU : U ∈ M.sets := M.union_mem unions hR
  have smallR : GroundBelow M R K := small.function_image pairing unions powers separation choice
    hD hS hK hProjection (productSecond_function rows S)
  have smallU : GroundBelow M U K := GroundBelow.sUnion pairing unions powers separation choice
    hR hK ordinal regular strong smallR (fun A hA =>
      GroundBelow.of_countable omega ((M.mem_groundSmallSubsets J ZFSet.omega A).1
        ((mem_relationImage D S projection A).1 hA).1).2.2)
  have subset : U ⊆ J := by
    intro z hz
    obtain ⟨A, hA, hz⟩ := ZFSet.mem_sUnion.1 hz
    have inS := ((mem_relationImage D S projection A).1 hA).1
    exact ((M.mem_groundSmallSubsets J ZFSet.omega A).1 inS).2.1 hz
  obtain ⟨beta, hBeta, cuts⟩ := M.small_assignmentCuts_bounded pairing unions powers separation
    hU hK (M.refinementDataHistoryLevels_mem pairing unions powers separation hK hHistory hT)
    regular smallU run.data.levels_function subset
  refine ⟨beta, hBeta, ?_⟩
  intro row A member
  have actual := members member
  have candidate := ((M.mem_refinementHistoryForcing rows T K history _).1 actual).1
  have pair : row ∈ rows ∧ A ∈ S := ZFSet.pair_mem_prod.1 candidate
  have inR : A ∈ R := (mem_relationImage D S projection A).2 ⟨pair.2, ZFSet.pair row A,
    member, (mem_productSecond rows S _).2 ⟨row, pair.1, A, pair.2, rfl⟩⟩
  have cut := cuts A (fun z hz => ZFSet.mem_sUnion.2 ⟨A, inR, hz⟩)
  exact ⟨cut, cut ▸ run.cut_mem actual hBeta⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def rawFlatForcingStage
    (Q rows rowOrder rowTop rowAction G J assignmentAction : ZFSet.{u}) : ZFSet.{u} :=
  forcingStageCode Q (rawRowAssignmentOrder Q rowOrder) (ZFSet.pair rowTop ∅)
    (rawRowAssignmentActionGraph G Q rows (⋃₀ ⋃₀ Q) J rowAction assignmentAction)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def definable_emptyFromGround :
    GroundDefinableFunction M (fun _env : Fin 1 → ZFSet.{u} => (∅ : ZFSet.{u})) where
  formula := (BoundedFormula.emptyFormula 0).toFormula
  closed := fun env members => M.empty_mem ⟨env 0, members 0⟩
  correct := by
    intro env members z hz
    exact (BoundedFormula.realize_toFormula M _ (extend z env) (Fin.cases hz members)).trans
      (BoundedFormula.truth_emptyFormula 0 _)

noncomputable def definable_rawFlatForcingStage
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      rawFlatForcingStage (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7)) := by
  let v := GroundSetTerm.var M (n := 8)
  let order := GroundSetTerm.app (M.definable_rawRowAssignmentOrder pairing unions powers separation) ![v 0, v 2]
  let emptyData := GroundSetTerm.app M.definable_emptyFromGround ![v 0]
  let top := GroundSetTerm.app (M.definable_nonemptyTuple pairing 1) ![v 3, emptyData]
  let dataBound := GroundSetTerm.app (M.definable_doubleUnion unions) ![v 0]
  let action := GroundSetTerm.app (M.definable_rawRowAssignmentActionGraph pairing unions powers separation collection)
    ![v 5, v 0, v 1, dataBound, v 6, v 4, v 7]
  exact (GroundSetTerm.app (M.definable_nonemptyTuple pairing 3) ![v 0, order, top, action]).definition

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def structuralForcingStageFromCarrier
    (Q rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  rawFlatForcingStage Q rows rowOrder rowTop rowAction G
    (M.structuralAssignments G nodes nodeOrder basis T T2 stages history)
    (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history)

noncomputable def definable_structuralForcingStageFromCarrier
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 14 → ZFSet.{u} =>
      M.structuralForcingStageFromCarrier (env 0) (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) (env 11) (env 12) (env 13)) := by
  let v := GroundSetTerm.var M (n := 14)
  let assignments := GroundSetTerm.app (M.definable_structuralAssignments pairing unions powers separation collection)
    ![v 5, v 6, v 7, v 9, v 10, v 11, v 12, v 13]
  let action := GroundSetTerm.app (M.definable_structuralAssignmentActionGraph pairing unions powers separation collection)
    ![v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13]
  exact (GroundSetTerm.app (M.definable_rawFlatForcingStage pairing unions powers separation collection)
    ![v 0, v 1, v 2, v 3, v 4, v 5, assignments, action]).definition





noncomputable def structuralForcingStage
    (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history : ZFSet.{u}) : ZFSet.{u} :=
  M.structuralForcingStageFromCarrier
    (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history)
    rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

include pairing unions powers separation collection in
theorem structuralForcingStage_mem (env : Fin 13 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.structuralForcingStage (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)
      (env 7) (env 8) (env 9) (env 10) (env 11) (env 12) ∈ M.sets := by
  have carrier := M.structuralForcingCarrier_mem pairing unions powers separation collection
    ![env 0, env 4, env 5, env 6, env 8, env 9, env 10, env 11, env 12]
    (Fin.cases (members 0) (Fin.cases (members 4) (Fin.cases (members 5)
      (Fin.cases (members 6) (Fin.cases (members 8) (Fin.cases (members 9)
        (Fin.cases (members 10) (Fin.cases (members 11) (Fin.cases (members 12) (fun j => Fin.elim0 j)))))))))) omega
  exact (M.definable_structuralForcingStageFromCarrier pairing unions powers separation collection).closed
    (extend _ env) (Fin.cases carrier members)

noncomputable def structuralForcingStageFormula {n : Nat}
    (output rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history N : Fin n) : SetFormula n :=
  .ex (.conj
    (M.structuralForcingCarrierFormula pairing unions powers separation collection
      0 rows.succ G.succ nodes.succ nodeOrder.succ basis.succ T.succ T2.succ stages.succ history.succ N.succ)
    (reindex (extend output.succ ![0, rows.succ, rowOrder.succ, rowTop.succ, rowAction.succ,
      G.succ, nodes.succ, nodeOrder.succ, nodeAction.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ])
      (M.definable_structuralForcingStageFromCarrier pairing unions powers separation collection).formula))

theorem realize_structuralForcingStageFormula {n : Nat}
    (output rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) (naturals : env N = ZFSet.omega) :
    Realize M.sets (M.structuralForcingStageFormula pairing unions powers separation collection
      output rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history N) env ↔
      env output = M.structuralForcingStage (env rows) (env rowOrder) (env rowTop) (env rowAction)
        (env G) (env nodes) (env nodeOrder) (env nodeAction) (env basis) (env T) (env T2) (env stages) (env history) := by
  unfold structuralForcingStageFormula
  rw [realize_ex]
  let params : Fin 13 → ZFSet.{u} := ![env rows, env rowOrder, env rowTop, env rowAction,
    env G, env nodes, env nodeOrder, env nodeAction, env basis, env T, env T2, env stages, env history]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases (members rows) (Fin.cases (members rowOrder)
    (Fin.cases (members rowTop) (Fin.cases (members rowAction) (Fin.cases (members G)
      (Fin.cases (members nodes) (Fin.cases (members nodeOrder) (Fin.cases (members nodeAction)
        (Fin.cases (members basis) (Fin.cases (members T) (Fin.cases (members T2)
          (Fin.cases (members stages) (Fin.cases (members history) (fun j => Fin.elim0 j)))))))))))))
  have args (Q : ZFSet.{u}) :
      (fun j : Fin 14 => extend Q env (![0, rows.succ, rowOrder.succ, rowTop.succ, rowAction.succ,
        G.succ, nodes.succ, nodeOrder.succ, nodeAction.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ] j)) =
      extend Q params := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))))))) j
  have meaning (Q : ZFSet.{u}) (hQ : Q ∈ M.sets) :
      Realize M.sets (.conj
        (M.structuralForcingCarrierFormula pairing unions powers separation collection
          0 rows.succ G.succ nodes.succ nodeOrder.succ basis.succ T.succ T2.succ stages.succ history.succ N.succ)
        (reindex (extend output.succ ![0, rows.succ, rowOrder.succ, rowTop.succ, rowAction.succ,
          G.succ, nodes.succ, nodeOrder.succ, nodeAction.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ])
          (M.definable_structuralForcingStageFromCarrier pairing unions powers separation collection).formula))
        (extend Q env) ↔
      Q = M.structuralForcingCarrier (env rows) (env G) (env nodes) (env nodeOrder) (env basis)
        (env T) (env T2) (env stages) (env history) ∧
      env output = M.structuralForcingStageFromCarrier Q (env rows) (env rowOrder) (env rowTop) (env rowAction)
        (env G) (env nodes) (env nodeOrder) (env nodeAction) (env basis) (env T) (env T2) (env stages) (env history) := by
    apply and_congr
    · exact M.realize_structuralForcingCarrierFormula pairing unions powers separation collection
        0 rows.succ G.succ nodes.succ nodeOrder.succ basis.succ T.succ T2.succ stages.succ history.succ N.succ
        (extend Q env) (Fin.cases hQ members) naturals
    · rw [realize_reindex, map_extend, args]
      exact (M.definable_structuralForcingStageFromCarrier pairing unions powers separation collection).correct
        (extend Q params) (Fin.cases hQ ground) (env output) (members output)
  constructor
  · rintro ⟨Q, hQ, holds⟩
    obtain ⟨rfl, equal⟩ := (meaning Q hQ).1 holds
    exact equal
  · intro equal
    have carrier := M.structuralForcingCarrier_mem pairing unions powers separation collection
      ![env rows, env G, env nodes, env nodeOrder, env basis, env T, env T2, env stages, env history]
      (Fin.cases (members rows) (Fin.cases (members G) (Fin.cases (members nodes)
        (Fin.cases (members nodeOrder) (Fin.cases (members basis) (Fin.cases (members T)
          (Fin.cases (members T2) (Fin.cases (members stages) (Fin.cases (members history) (fun j => Fin.elim0 j))))))))))
      (naturals ▸ members N)
    exact ⟨_, carrier, (meaning _ carrier).2 ⟨rfl, equal⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

noncomputable def structuralForcingStepFormula : SetFormula 15 :=
  M.structuralForcingStageFormula pairing unions powers separation collection
    2 3 4 5 6 7 8 9 10 11 12 13 0 1 14

theorem realize_structuralForcingStepFormula (params : Fin 12 → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) (naturals : params 11 = ZFSet.omega)
    {alpha prior output : ZFSet.{u}} (ha : alpha ∈ M.sets) (hp : prior ∈ M.sets) (ho : output ∈ M.sets) :
    Realize M.sets (M.structuralForcingStepFormula pairing unions powers separation collection)
      (extend alpha (extend prior (extend output params))) ↔
    output = M.structuralForcingStage (params 0) (params 1) (params 2) (params 3) (params 4)
      (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) alpha prior :=
  M.realize_structuralForcingStageFormula pairing unions powers separation collection
    2 3 4 5 6 7 8 9 10 11 12 13 0 1 14 _ (Fin.cases ha (Fin.cases hp (Fin.cases ho members))) naturals

theorem structuralForcingStepClosure (params : Fin 12 → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) (naturals : params 11 = ZFSet.omega)
    {stages : ZFSet.{u}} (hs : stages ∈ M.sets) :
    GroundOrdinalStepClosure M stages (M.structuralForcingStepFormula pairing unions powers separation collection) params := by
  intro alpha halpha prior hprior _trace
  have ha := M.transitive hs halpha
  let args : Fin 13 → ZFSet.{u} := ![params 0,params 1,params 2,params 3,params 4,params 5,
    params 6,params 7,params 8,params 9,params 10,alpha,prior]
  have ground : ∀ j, args j ∈ M.sets := by
    exact Fin.cases (members 0) (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3)
      (Fin.cases (members 4) (Fin.cases (members 5) (Fin.cases (members 6) (Fin.cases (members 7)
        (Fin.cases (members 8) (Fin.cases (members 9) (Fin.cases (members 10)
          (Fin.cases ha (Fin.cases hprior (fun j => Fin.elim0 j)))))))))))))
  have outputGround := M.structuralForcingStage_mem pairing unions powers separation collection args ground
    (naturals ▸ members 11)
  refine ⟨_, outputGround, ?_, ?_⟩
  · exact (M.realize_structuralForcingStepFormula pairing unions powers separation collection params members naturals
      ha hprior outputGround).2 rfl
  · intro output ho recognized
    exact (M.realize_structuralForcingStepFormula pairing unions powers separation collection params members naturals
      ha hprior ho).1 recognized

theorem exists_structuralForcingTrace (params : Fin 12 → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) (naturals : params 11 = ZFSet.omega)
    {stages : ZFSet.{u}} (hs : stages ∈ M.sets) (ordinal : ordinalSetProperty stages) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M
        (M.structuralForcingStepFormula pairing unions powers separation collection) params) stages history ∧
      OrdinalRecursionTrace (fun alpha prior output =>
        output = M.structuralForcingStage (params 0) (params 1) (params 2) (params 3) (params 4)
          (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) alpha prior) stages history ∧
      (∀ other, OrdinalRecursionTrace (groundRecursionStep M
        (M.structuralForcingStepFormula pairing unions powers separation collection) params) stages other → other = history) ∧
      ∀ alpha ∈ stages, ∀ output ∈ M.sets,
        ZFSet.pair alpha output ∈ history ↔
          output = M.structuralForcingStage (params 0) (params 1) (params 2) (params 3) (params 4)
            (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) alpha (graphRestriction alpha history) := by
  obtain ⟨history, hh, trace, unique, entry⟩ := M.exists_unique_ordinalRecursionTrace pairing unions separation collection
    hs ordinal (M.structuralForcingStepFormula pairing unions powers separation collection) params members
    (M.structuralForcingStepClosure pairing unions powers separation collection params members naturals hs)
  refine ⟨history, hh, trace, ⟨trace.1, ?_⟩, unique, ?_⟩
  · intro alpha halpha output stored
    have step := trace.2 alpha halpha output stored
    exact (M.realize_structuralForcingStepFormula pairing unions powers separation collection params members naturals
      (M.transitive hs halpha) step.1 step.2.1).1 step.2.2
  intro alpha halpha output ho
  have ha := M.transitive hs halpha
  exact (entry alpha halpha output ho).trans
    (M.realize_structuralForcingStepFormula pairing unions powers separation collection params members naturals
      ha (M.graphRestriction_mem unions separation ha hh) ho)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u}
variable [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (rows rowOrder rowTop rowAction T T2 : ZFSet.{u})
local notation "step" => fun level prior output =>
  output = M.structuralForcingStage rows rowOrder rowTop rowAction t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior

theorem structuralTrace_prefix_ground
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {stages history : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages) (trace : OrdinalRecursionTrace step stages history)
    {level P order top action : ZFSet.{u}}
    (stored : ZFSet.pair level (forcingStageCode P order top action) ∈ history) :
    level ∈ M.sets ∧ ordinalSetProperty level ∧ graphRestriction level history ∈ M.sets ∧
      OrdinalRecursionTrace step level (graphRestriction level history) ∧
      P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets := by
  have member := trace.1.pair_source stored
  have hLevel := M.transitive hStages member
  have levelOrdinal := ordinalSetProperty_member ordinal member
  have codeGround := M.transitive (M.union_mem unions (M.union_mem unions hHistory))
    (pair_second_mem_doubleUnion stored)
  exact ⟨hLevel, levelOrdinal, M.graphRestriction_mem unions separation hLevel hHistory,
    trace.restrict levelOrdinal (ordinal.1 level member), M.forcingStageCode_fields codeGround⟩

theorem structuralTrace_stageWitnesses
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (current : ∀ level prior, level ∈ M.sets → prior ∈ M.sets → ordinalSetProperty level →
      OrdinalRecursionTrace step level prior →
      (∀ earlier P order top action, ZFSet.pair earlier (forcingStageCode P order top action) ∈ prior →
        RawRefinementStageWitness M t b d base directed T T2 earlier P order top action) →
      ∀ P order top action,
        forcingStageCode P order top action =
          M.structuralForcingStage rows rowOrder rowTop rowAction t.carrier b.carrier b.conditionOrder
            (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior →
        RawRefinementStageWitness M t b d base directed T T2 level P order top action)
    {stages history : ZFSet.{u}} (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages) (trace : OrdinalRecursionTrace step stages history) :
    ∀ level P order top action, ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      RawRefinementStageWitness M t b d base directed T T2 level P order top action := by
  intro level
  induction level using ZFSet.inductionOn with
  | h level ih =>
    intro P order top action stored
    obtain ⟨hLevel, levelOrdinal, hPrefix, prefixTrace, _fields⟩ :=
      M.structuralTrace_prefix_ground t b d rows rowOrder rowTop rowAction T T2
        unions separation hStages hHistory ordinal trace stored
    apply current level (graphRestriction level history) hLevel hPrefix levelOrdinal prefixTrace
    · intro earlier P' order' top' action' entry
      have prefixEntry := pair_mem_graphRestriction.1 entry
      exact ih earlier prefixEntry.2 P' order' top' action' prefixEntry.1
    · exact trace.2 level (trace.1.pair_source stored) _ stored

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralForcingStage_eq (stages history : ZFSet.{u}) :
    M.structuralForcingStage rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history =
    forcingStageCode
      (M.refinementHistoryForcing rows T stages
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history))
      (M.refinementHistoryOrder rows rowOrder T stages
        (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history))
      (ZFSet.pair rowTop ∅)
      (rawRowAssignmentActionGraph G
        (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history)
        rows (⋃₀ ⋃₀ (M.structuralForcingCarrier rows G nodes nodeOrder basis T T2 stages history))
        (M.structuralAssignments G nodes nodeOrder basis T T2 stages history) rowAction
        (M.structuralAssignmentActionGraph G nodes nodeOrder nodeAction basis T T2 stages history)) := by
  unfold structuralForcingStage structuralForcingStageFromCarrier rawFlatForcingStage structuralForcingCarrier
  rw [M.refinementHistoryOrder_raw]

theorem structuralForcingTrace_recursiveOrder {stages history : ZFSet.{u}}
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace
      (fun level prior stage => stage = M.structuralForcingStage rows rowOrder rowTop rowAction
        G nodes nodeOrder nodeAction basis T T2 level prior) stages history) :
    RecursiveRefinementOrderHistory M rows rowOrder T stages
      (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history) := by
  apply M.structuralRefinementHistory_recursiveOrder_of_trace G nodes nodeOrder basis T T2
    rows rowOrder stages history ordinal trace
  intro level prior stage equal
  exact ⟨_, _, equal.trans (M.structuralForcingStage_eq rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 level prior)⟩

theorem structuralForcingTrace_stageOrderTop {stages history : ZFSet.{u}}
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace
      (fun level prior stage => stage = M.structuralForcingStage rows rowOrder rowTop rowAction
        G nodes nodeOrder nodeAction basis T T2 level prior) stages history)
    (hRows : rows ∈ M.sets) (rowOrderLaw : PartialOrderCode rows rowOrder)
    (topMem : rowTop ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row rowTop ∈ rowOrder) :
    ∀ level P order top action, ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      PartialOrderCode P order ∧ top ∈ P ∧ ∀ p ∈ P, ZFSet.pair p top ∈ order := by
  intro level P order top action stored
  have hl := trace.1.pair_source stored
  have cutOrdinal := ordinalSetProperty_member ordinal hl
  have earlier := trace.restrict cutOrdinal (ordinal.1 level hl)
  have run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 cutOrdinal earlier
  have equal := (trace.2 level hl _ stored).trans
    (M.structuralForcingStage_eq rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2
      level (graphRestriction level history))
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 equal
  exact ⟨M.refinementHistoryOrder_partialOrder rowOrderLaw T level _,
    run.carriers.empty_assignments cutOrdinal hRows topMem,
    run.carriers.greatest cutOrdinal hRows topMem topRows⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem structuralForcingTrace_small_family_prefix
    (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hRows : rows ∈ M.sets) (hG : G ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hNodeOrder : nodeOrder ∈ M.sets) (hBasis : basis ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hHistory : history ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (trace : OrdinalRecursionTrace
      (fun level prior stage => stage = M.structuralForcingStage rows rowOrder rowTop rowAction
        G nodes nodeOrder nodeAction basis T T2 level prior) K history) :
    let packed := M.structuralRefinementHistory G nodes nodeOrder basis T T2 K history
    ∀ D ∈ M.sets, GroundBelow M D K → D ⊆ M.refinementHistoryForcing rows T K packed →
      ∃ beta ∈ K, ∀ row A, ZFSet.pair row A ∈ D →
        assignmentCut (refinementDataHistoryLevels K packed T) beta A = A ∧
        ZFSet.pair row A ∈ M.refinementHistoryForcing rows T beta (graphRestriction beta packed) := by
  dsimp only
  intro D hD small members
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, K, history]
    (Fin.cases hG (Fin.cases hNodes (Fin.cases hNodeOrder (Fin.cases hBasis
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
  have run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 conditions.1 trace
  exact M.small_refinementConditionFamily_prefix pairing unions powers separation choice hRows hT hK
    packed hD conditions.1 conditions.2.1 conditions.2.2.1 conditions.2.2.2 run.carriers small members





theorem exists_structuralForcingHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (params : Fin 12 → ZFSet.{u}) (members : ∀ j, params j ∈ M.sets)
    (naturals : params 11 = ZFSet.omega)
    {stages : ZFSet.{u}} (hStages : stages ∈ M.sets) (ordinal : ordinalSetProperty stages)
    (rowOrderLaw : PartialOrderCode (params 0) (params 1))
    (topMem : params 2 ∈ params 0)
    (topRows : ∀ row ∈ params 0, ZFSet.pair row (params 2) ∈ params 1) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (fun level prior stage =>
        stage = M.structuralForcingStage (params 0) (params 1) (params 2) (params 3) (params 4)
          (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) level prior) stages history ∧
      M.structuralRefinementHistory (params 4) (params 5) (params 6) (params 8) (params 9) (params 10)
        stages history ∈ M.sets ∧
      RecursiveRefinementOrderHistory M (params 0) (params 1) (params 9) stages
        (M.structuralRefinementHistory (params 4) (params 5) (params 6) (params 8) (params 9) (params 10)
          stages history) ∧
      ∀ level P order top action, ZFSet.pair level (forcingStageCode P order top action) ∈ history →
        PartialOrderCode P order ∧ top ∈ P ∧ ∀ p ∈ P, ZFSet.pair p top ∈ order := by
  obtain ⟨history, hHistory, _groundTrace, trace, _unique, _lookup⟩ :=
    M.exists_structuralForcingTrace pairing unions powers separation collection params members naturals hStages ordinal
  refine ⟨history, hHistory, trace, ?_, ?_, ?_⟩
  · exact (M.definable_structuralRefinementHistory pairing unions powers separation collection).closed
      ![params 4, params 5, params 6, params 8, params 9, params 10, stages, history]
      (Fin.cases (members 4) (Fin.cases (members 5) (Fin.cases (members 6)
        (Fin.cases (members 8) (Fin.cases (members 9) (Fin.cases (members 10)
          (Fin.cases hStages (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
  · exact M.structuralForcingTrace_recursiveOrder (params 0) (params 1) (params 2) (params 3)
      (params 4) (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) ordinal trace
  · exact M.structuralForcingTrace_stageOrderTop (params 0) (params 1) (params 2) (params 3)
      (params 4) (params 5) (params 6) (params 7) (params 8) (params 9) (params 10)
      ordinal trace (members 0) rowOrderLaw topMem topRows

end PartitionPilot.Forcing.TransitiveGround

end OAI
