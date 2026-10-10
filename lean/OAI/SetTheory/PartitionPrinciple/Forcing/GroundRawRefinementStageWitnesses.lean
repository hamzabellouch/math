import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRawStageRefinementTestActions

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def forcingStageCode (P order top action : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 3 ![P, order, top, action]

theorem forcingStageCode_eq_iff (P order top action P' order' top' action' : ZFSet.{u}) :
    forcingStageCode P order top action = forcingStageCode P' order' top' action' ↔
      P = P' ∧ order = order' ∧ top = top' ∧ action = action' := by
  simp only [forcingStageCode, nonemptyTupleCode, ZFSet.pair_inj]
  rfl

def ForcingStageValidityCode (G mul identity stage : ZFSet.{u}) : Prop :=
  ∃ P order top action, stage = forcingStageCode P order top action ∧
    PartialOrderCode P order ∧ top ∈ P ∧
    (∀ p ∈ P, ZFSet.pair p top ∈ order) ∧ PosetActionCode G P mul identity order action

theorem forcingStageValidityCode_iff (G mul identity P order top action : ZFSet.{u}) :
    ForcingStageValidityCode G mul identity (forcingStageCode P order top action) ↔
      PartialOrderCode P order ∧ top ∈ P ∧
      (∀ p ∈ P, ZFSet.pair p top ∈ order) ∧ PosetActionCode G P mul identity order action := by
  constructor
  · rintro ⟨P', r', t', A', equal, laws⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 equal
    exact laws
  · intro laws
    exact ⟨P, order, top, action, rfl, laws⟩

namespace BoundedFormula
open SetFormula

def forcingStageFormula {n : Nat} (stage G mul identity : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  exPairFields stage (exPairFields 0 (exPairFields 0
    (.conj (partialOrderFormula 5 3)
      (.conj (topFormula 5 3 1) (posetActionFormula (lift G) 5 (lift mul) (lift identity) 3 0)))))

theorem truth_forcingStageFormula {n : Nat} (stage G mul identity : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (forcingStageFormula stage G mul identity) env ↔
      ForcingStageValidityCode (env G) (env mul) (env identity) (env stage) := by
  simp only [forcingStageFormula, truth_exPairFields, Truth, truth_partialOrderFormula,
    truth_topFormula, truth_posetActionFormula]
  change (∃ P tail, env stage = ZFSet.pair P tail ∧
    ∃ order tail', tail = ZFSet.pair order tail' ∧
    ∃ top action, tail' = ZFSet.pair top action ∧
      PartialOrderCode P order ∧ (top ∈ P ∧ ∀ p ∈ P, ZFSet.pair p top ∈ order) ∧
      PosetActionCode (env G) P (env mul) (env identity) order action) ↔ _
  constructor
  · rintro ⟨P, tail, equal, order, tail', eqtail, top, action, eqtail', orderLaw, ⟨member, greatest⟩, act⟩
    refine ⟨P, order, top, action, ?_, orderLaw, member, greatest, act⟩
    rw [eqtail, eqtail'] at equal
    exact equal
  · rintro ⟨P, order, top, action, equal, orderLaw, member, greatest, act⟩
    exact ⟨P, ZFSet.pair order (ZFSet.pair top action), equal,
      order, ZFSet.pair top action, rfl, top, action, rfl, orderLaw, ⟨member, greatest⟩, act⟩

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem forcingStageCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {P order top action : ZFSet.{u}}
    (hP : P ∈ M.sets) (hOrder : order ∈ M.sets) (hTop : top ∈ M.sets) (hAction : action ∈ M.sets) :
    forcingStageCode P order top action ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 3 _
    (Fin.cases hP (Fin.cases hOrder (Fin.cases hTop (Fin.cases hAction (fun j => Fin.elim0 j)))))

theorem forcingStageCode_fields {P order top action : ZFSet.{u}}
    (ground : forcingStageCode P order top action ∈ M.sets) :
    P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets := by
  have fields := M.nonemptyTupleCode_field_mem 3 ![P, order, top, action] ground
  exact ⟨fields 0, fields 1, fields 2, fields 3⟩

theorem realize_forcingStageFormula {n : Nat} (stage G mul identity : Fin n)
    (env : Fin n → ZFSet.{u}) (ground : ∀ j, env j ∈ M.sets) :
    Realize M.sets (BoundedFormula.forcingStageFormula stage G mul identity).toFormula env ↔
      ForcingStageValidityCode (env G) (env mul) (env identity) (env stage) :=
  (BoundedFormula.realize_toFormula M _ _ ground).trans
    (BoundedFormula.truth_forcingStageFormula stage G mul identity env)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

structure ForcingStageCore (G mul identity : ZFSet.{u}) where
  carrier : ZFSet.{u}
  order : ZFSet.{u}
  top : ZFSet.{u}
  actionGraph : ZFSet.{u}
  order_code : PartialOrderCode carrier order
  top_mem : top ∈ carrier
  greatest : ∀ p ∈ carrier, ZFSet.pair p top ∈ order
  action_code : PosetActionCode G carrier mul identity order actionGraph

namespace ForcingStageCore
variable {G mul identity : ZFSet.{u}} (core : ForcingStageCore G mul identity)

noncomputable def code : ZFSet.{u} :=
  forcingStageCode core.carrier core.order core.top core.actionGraph

theorem validity : ForcingStageValidityCode G mul identity core.code :=
  (forcingStageValidityCode_iff _ _ _ _ _ _ _).2
    ⟨core.order_code, core.top_mem, core.greatest, core.action_code⟩

noncomputable def presentation : Presentation (SetMembers core.carrier) :=
  SetMembers.presentation core.carrier

@[instance_reducible] noncomputable def partialOrder : PartialOrder (SetMembers core.carrier) :=
  core.order_code.toPartialOrder

@[instance_reducible] noncomputable def orderTop :
    letI := core.partialOrder
    OrderTop (SetMembers core.carrier) :=
  core.order_code.toOrderTop core.top core.top_mem core.greatest

noncomputable def action {inverse : ZFSet.{u}} (group : GroupCode G mul inverse identity) :
    letI := group.toGroup
    letI := core.partialOrder
    PosetAction (SetMembers G) (SetMembers core.carrier) :=
  core.action_code.toPosetAction group core.order_code

theorem decoded_code {inverse : ZFSet.{u}} (group : GroupCode G mul inverse identity) :
    letI := group.toGroup
    letI := core.partialOrder
    letI := core.orderTop
    forcingStageCode core.presentation.carrier core.presentation.conditionOrder
      (core.presentation.encode ⊤)
      ((core.action group).actionGraph core.presentation (SetMembers.presentation G)) = core.code := by
  let := group.toGroup
  let := core.partialOrder
  let := core.orderTop
  change forcingStageCode core.carrier
    ((SetMembers.presentation core.carrier).conditionOrder)
    (SetMembers.raw (SetMembers.ofMem core.top core.top_mem))
    ((core.action_code.toPosetAction group core.order_code).actionGraph
      (SetMembers.presentation core.carrier) (SetMembers.presentation G)) = core.code
  rw [core.order_code.conditionOrder_eq, SetMembers.raw_ofMem,
    core.action_code.actionGraph_eq group core.order_code]
  rfl

end ForcingStageCore

theorem exists_forcingStageCore {G mul identity stage : ZFSet.{u}}
    (valid : ForcingStageValidityCode G mul identity stage) :
    ∃ core : ForcingStageCore G mul identity, core.code = stage := by
  obtain ⟨P, order, top, action, equal, orderLaw, member, greatest, act⟩ := valid
  exact ⟨⟨P, order, top, action, orderLaw, member, greatest, act⟩, equal.symm⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem forcingStageCore_conditionMapFamily_mem {G mul identity inverse : ZFSet.{u}}
    (core : ForcingStageCore G mul identity) (group : GroupCode G mul inverse identity)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hG : G ∈ M.sets) (ground : core.code ∈ M.sets) :
    letI := group.toGroup
    letI := core.partialOrder
    (core.action group).conditionMapFamily core.presentation (SetMembers.presentation G) ∈ M.sets := by
  let := group.toGroup
  let := core.partialOrder
  obtain ⟨hP, _, _, hA⟩ := M.forcingStageCode_fields ground
  apply M.conditionMapFamily_mem_of_actionGraph (core.action group) core.presentation
    (SetMembers.presentation G) pairing unions powers separation collection hP hG
  change (core.action_code.toPosetAction group core.order_code).actionGraph
    (SetMembers.presentation core.carrier) (SetMembers.presentation G) ∈ M.sets
  rw [core.action_code.actionGraph_eq group core.order_code]
  exact hA

end TransitiveGround

end PartitionPilot.Forcing


section

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {P : Type u} [PartialOrder P] (s : Presentation P)

theorem conditionOrder_code : PartialOrderCode s.carrier s.conditionOrder := by
  refine ⟨(s.product s).subset_carrier _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact (s.pair_mem_conditionOrder x x).2 le_rfl
  · intro x hx y hy xy yx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    exact congrArg s.encode (le_antisymm ((s.pair_mem_conditionOrder x y).1 xy)
      ((s.pair_mem_conditionOrder y x).1 yx))
  · intro x hx y hy z hz xy yz
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    exact (s.pair_mem_conditionOrder x z).2 (le_trans
      ((s.pair_mem_conditionOrder x y).1 xy) ((s.pair_mem_conditionOrder y z).1 yz))

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem actionGraph_code : PosetActionCode t.carrier s.carrier
    ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
    s.conditionOrder (a.actionGraph s t) := by
  refine ⟨(t.product s).graph_isFunc s _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact (a.triple_mem_actionGraph s t 1 x x).2 (a.one x)
  · intro g hg h hh k hk x hx y hy z hz gh xy yz
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨h, rfl⟩ := (t.mem_carrier h).1 hh
    obtain ⟨k, rfl⟩ := (t.mem_carrier k).1 hk
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    have product := ((t.product t).pair_mem_graph t _ (g, h) k).1 gh
    have first := (a.triple_mem_actionGraph s t h x y).1 xy
    have second := (a.triple_mem_actionGraph s t g y z).1 yz
    apply (a.triple_mem_actionGraph s t k x z).2
    rw [← product, a.mul, first, second]
  · intro g hg x hx y hy z hz w hw xz yw xy
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    have first := (a.triple_mem_actionGraph s t g x z).1 xz
    have second := (a.triple_mem_actionGraph s t g y w).1 yw
    apply (s.pair_mem_conditionOrder z w).2
    rw [← first, ← second]
    exact (a.iso g).monotone ((s.pair_mem_conditionOrder x y).1 xy)

noncomputable def forcingStageCore [OrderTop P] :
    ForcingStageCore t.carrier ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1) where
  carrier := s.carrier
  order := s.conditionOrder
  top := s.encode ⊤
  actionGraph := a.actionGraph s t
  order_code := s.conditionOrder_code
  top_mem := s.encode_mem ⊤
  greatest := by
    intro p hp
    obtain ⟨p, rfl⟩ := (s.mem_carrier p).1 hp
    exact (s.pair_mem_conditionOrder p ⊤).2 le_top
  action_code := a.actionGraph_code s t

theorem forcingStageCore_code [OrderTop P] :
    (a.forcingStageCore s t).code = forcingStageCode s.carrier s.conditionOrder
      (s.encode ⊤) (a.actionGraph s t) := rfl

end PartitionPilot.Forcing.PosetAction

end


namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G L : Type u} [Group G] [PartialOrder L]

def RawRefinementStageWitness (M : TransitiveGround.{u})
    (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T T2 level P order top action : ZFSet.{u}) : Prop :=
  ∃ (orderLaw : PartialOrderCode P order) (topMem : top ∈ P)
    (greatest : ∀ p ∈ P, ZFSet.pair p top ∈ order),
    letI := orderLaw.toPartialOrder
    letI := orderLaw.toOrderTop top topMem greatest
    ∃ e : PosetAction G (SetMembers P),
      e.actionGraph (SetMembers.presentation P) t = action ∧
      RefinementStageSystem M e (SetMembers.presentation P) t b d base directed level T T2

namespace RawRefinementStageWitness
variable {M : TransitiveGround.{u}} {t : Presentation G} {b : Presentation L}
variable {d : PosetAction G L} {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}
variable (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)
include witness

theorem action_code : PosetActionCode t.carrier P
    ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1) order action := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, _system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have code := e.actionGraph_code (SetMembers.presentation P) t
  rw [orderLaw.conditionOrder_eq, graph] at code
  exact code

theorem action_function : ZFSet.IsFunc (ZFSet.prod t.carrier P) P action :=
  witness.action_code.function

end RawRefinementStageWitness

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
open SetFormula
universe u

def ForcingStageRefinementDataCode (M : TransitiveGround.{u})
    (G mul identity nodes nodeOrder basis T T2 level stage output : ZFSet.{u}) : Prop :=
  ForcingStageValidityCode G mul identity stage ∧
    ∃ P order top action, stage = forcingStageCode P order top action ∧
      output = M.rawRefinementFormulaDataCode P order top action G nodes nodeOrder basis T T2 level

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

noncomputable def forcingStageRefinementDataFormula : SetFormula 11 :=
  let w := prefixIndex 11 4
  let old := suffixIndex 11 4
  .conj (BoundedFormula.forcingStageFormula 1 2 3 4).toFormula
    (exBlock 4 (.conj (BoundedFormula.nonemptyTupleFormula 3 (old 1) w).toFormula
      (SetFormula.reindex (extend (old 0)
        ![w 0, w 1, w 2, w 3, old 2, old 5, old 6, old 7, old 8, old 9, old 10])
        (M.definable_rawRefinementFormulaDataCode pairing unions powers separation collection).formula)))

theorem realize_forcingStageRefinementDataFormula (env : Fin 11 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.forcingStageRefinementDataFormula pairing unions powers separation collection) env ↔
      ForcingStageRefinementDataCode M (env 2) (env 3) (env 4) (env 5) (env 6) (env 7)
        (env 8) (env 9) (env 10) (env 1) (env 0) := by
  change (Realize M.sets (BoundedFormula.forcingStageFormula 1 2 3 4).toFormula env ∧ _) ↔ _
  rw [M.realize_forcingStageFormula 1 2 3 4 env members]
  apply and_congr_right
  intro _
  rw [realize_exBlock]
  have meaning (fields : Fin 4 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets (.conj (BoundedFormula.nonemptyTupleFormula 3 (suffixIndex 11 4 1)
        (prefixIndex 11 4)).toFormula
        (SetFormula.reindex (extend (suffixIndex 11 4 0)
          ![prefixIndex 11 4 0, prefixIndex 11 4 1, prefixIndex 11 4 2, prefixIndex 11 4 3,
            suffixIndex 11 4 2, suffixIndex 11 4 5, suffixIndex 11 4 6, suffixIndex 11 4 7,
            suffixIndex 11 4 8, suffixIndex 11 4 9, suffixIndex 11 4 10])
          (M.definable_rawRefinementFormulaDataCode pairing unions powers separation collection).formula))
          (extendMany 4 fields env) ↔
        env 1 = nonemptyTupleCode 3 fields ∧
          env 0 = M.rawRefinementFormulaDataCode (fields 0) (fields 1) (fields 2) (fields 3)
            (env 2) (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) := by
    change (Realize M.sets (BoundedFormula.nonemptyTupleFormula 3 _ _).toFormula _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 4 fields env ground members),
      BoundedFormula.truth_nonemptyTupleFormula]
    simp only [extendMany_suffix, extendMany_prefix]
    apply and_congr_right
    intro _
    rw [realize_reindex, map_extend]
    have args : (fun j : Fin 11 => extendMany 4 fields env
      (![prefixIndex 11 4 0, prefixIndex 11 4 1, prefixIndex 11 4 2, prefixIndex 11 4 3,
        suffixIndex 11 4 2, suffixIndex 11 4 5, suffixIndex 11 4 6, suffixIndex 11 4 7,
        suffixIndex 11 4 8, suffixIndex 11 4 9, suffixIndex 11 4 10] j)) =
      ![fields 0, fields 1, fields 2, fields 3, env 2, env 5, env 6, env 7, env 8, env 9, env 10] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
          (Fin.cases rfl (fun k => Fin.elim0 k))))))))))) j
    rw [args]
    have argMembers : ∀ j, (![fields 0, fields 1, fields 2, fields 3, env 2, env 5, env 6,
        env 7, env 8, env 9, env 10] : Fin 11 → ZFSet.{u}) j ∈ M.sets :=
      (Fin.cases (ground 0) (Fin.cases (ground 1) (Fin.cases (ground 2) (Fin.cases (ground 3) (Fin.cases (members 2) (Fin.cases (members 5) (Fin.cases (members 6) (Fin.cases (members 7) (Fin.cases (members 8) (Fin.cases (members 9) (Fin.cases (members 10) (fun j => Fin.elim0 j))))))))))))
    exact (M.definable_rawRefinementFormulaDataCode pairing unions powers separation collection).correct _
      argMembers _ (members 0)
  constructor
  · rintro ⟨fields, ground, recognized⟩
    obtain ⟨shape, output⟩ := (meaning fields ground).1 recognized
    have eta : fields = ![fields 0, fields 1, fields 2, fields 3] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j
    exact ⟨fields 0, fields 1, fields 2, fields 3, eta ▸ shape, output⟩
  · rintro ⟨P, order, top, action, shape, output⟩
    have fields := M.forcingStageCode_fields (shape ▸ members 1)
    have ground : ∀ j, (![P, order, top, action] : Fin 4 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases fields.1 (Fin.cases fields.2.1
        (Fin.cases fields.2.2.1 (Fin.cases fields.2.2.2 (fun j => Fin.elim0 j))))
    exact ⟨![P, order, top, action], ground, (meaning _ ground).2 ⟨shape, output⟩⟩

end TransitiveGround





theorem ForcingStageRefinementDataCode.unique {M : TransitiveGround.{u}}
    {G mul identity nodes nodeOrder basis T T2 level stage x y : ZFSet.{u}}
    (first : ForcingStageRefinementDataCode M G mul identity nodes nodeOrder basis T T2 level stage x)
    (second : ForcingStageRefinementDataCode M G mul identity nodes nodeOrder basis T T2 level stage y) : x = y := by
  obtain ⟨_, P, order, top, action, stageEq, output⟩ := first
  obtain ⟨_, P', order', top', action', stageEq', output'⟩ := second
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 (stageEq.symm.trans stageEq')
  exact output.trans output'.symm

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem exists_forcingStageRefinementData (params : Fin 9 → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) {stage : ZFSet.{u}} (hStage : stage ∈ M.sets)
    (valid : ForcingStageValidityCode (params 0) (params 1) (params 2) stage) :
    ∃ output ∈ M.sets, ForcingStageRefinementDataCode M (params 0) (params 1) (params 2)
      (params 3) (params 4) (params 5) (params 6) (params 7) (params 8) stage output := by
  have shape := valid
  obtain ⟨P, order, top, action, equal, _⟩ := shape
  have fields := M.forcingStageCode_fields (equal ▸ hStage)
  let args : Fin 11 → ZFSet.{u} := ![P, order, top, action, params 0, params 3, params 4,
    params 5, params 6, params 7, params 8]
  have ground : ∀ j, args j ∈ M.sets :=
    Fin.cases fields.1 (Fin.cases fields.2.1 (Fin.cases fields.2.2.1 (Fin.cases fields.2.2.2
      (Fin.cases (members 0) (Fin.cases (members 3) (Fin.cases (members 4)
        (Fin.cases (members 5) (Fin.cases (members 6) (Fin.cases (members 7)
          (Fin.cases (members 8) (fun j => Fin.elim0 j)))))))))))
  exact ⟨_, (M.definable_rawRefinementFormulaDataCode pairing unions powers separation collection).closed args ground,
    valid, P, order, top, action, equal, rfl⟩

theorem exists_forcingStageRefinementGraph (params : Fin 9 → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) {stages : ZFSet.{u}} (hStages : stages ∈ M.sets)
    (valid : ∀ stage ∈ stages, ForcingStageValidityCode (params 0) (params 1) (params 2) stage) :
    ∃ graph ∈ M.sets, FunctionGraphOn stages graph ∧ ∀ stage output,
      ZFSet.pair stage output ∈ graph ↔ stage ∈ stages ∧
        ForcingStageRefinementDataCode M (params 0) (params 1) (params 2) (params 3)
          (params 4) (params 5) (params 6) (params 7) (params 8) stage output := by
  let formula := SetFormula.reindex (extend 1 (extend 0 (fun j : Fin 9 => j.succ.succ)))
    (M.forcingStageRefinementDataFormula pairing unions powers separation collection)
  have meaning (stage output : ZFSet.{u}) (hs : stage ∈ M.sets) (ho : output ∈ M.sets) :
      Realize M.sets formula (extend stage (extend output params)) ↔
        ForcingStageRefinementDataCode M (params 0) (params 1) (params 2) (params 3)
          (params 4) (params 5) (params 6) (params 7) (params 8) stage output := by
    rw [realize_reindex, map_extend, map_extend]
    exact M.realize_forcingStageRefinementDataFormula pairing unions powers separation collection _
      (Fin.cases ho (Fin.cases hs members))
  obtain ⟨B, hB, bounded⟩ := M.collection_witness collection formula params members hStages (by
    intro stage member
    obtain ⟨output, ground, relation⟩ := M.exists_forcingStageRefinementData pairing unions powers separation collection
      params members (M.transitive hStages member) (valid stage member)
    exact ⟨output, ground, (meaning stage output (M.transitive hStages member) ground).2 relation⟩)
  let graph := M.definableRelation formula params stages B
  have exactEntry (stage output : ZFSet.{u}) :
      ZFSet.pair stage output ∈ graph ↔ stage ∈ stages ∧
        ForcingStageRefinementDataCode M (params 0) (params 1) (params 2) (params 3)
          (params 4) (params 5) (params 6) (params 7) (params 8) stage output := by
    rw [M.pair_mem_definableRelation]
    constructor
    · rintro ⟨hs, ho, relation⟩
      exact ⟨hs, (meaning stage output (M.transitive hStages hs) (M.transitive hB ho)).1 relation⟩
    · rintro ⟨hs, relation⟩
      obtain ⟨y, hy, chosen⟩ := bounded stage hs
      have eq : output = y := relation.unique
        ((meaning stage y (M.transitive hStages hs) (M.transitive hB hy)).1 chosen)
      exact eq.symm ▸ ⟨hs, hy, chosen⟩
  refine ⟨graph, M.definableRelation_mem pairing unions powers separation formula params members hStages hB,
    ⟨B, ?_, ?_⟩, exactEntry⟩
  · exact fun _ member => (ZFSet.mem_sep.1 member).1
  · intro stage member
    obtain ⟨output, ho, relation⟩ := bounded stage member
    refine ⟨output, (M.pair_mem_definableRelation formula params stages B stage output).2 ⟨member, ho, relation⟩, ?_⟩
    intro y hy
    exact ((exactEntry stage y).1 hy).2.unique
      ((meaning stage output (M.transitive hStages member) (M.transitive hB ho)).1 relation)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RawRefinementStageWitness
open SetRealization SetFormula
universe u
variable {G L : Type u} [Group G] [PartialOrder L]
variable {M : TransitiveGround.{u}} {t : Presentation G} {b : Presentation L}
variable {d : PosetAction G L} {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}
variable (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : P ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (groundOrder : order ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets)
local notation "data" => M.rawRefinementFormulaData P order top action
  t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
include witness pairing unions powers separation collection carrier group nodes groundOrder supports hT

theorem rawTests_order_mono (A p q : ZFSet.{u})
    (tests : stageOneRawTests M data A p) (below : ZFSet.pair q p ∈ data 8) :
    stageOneRawTests M data A q := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  have topEq : (SetMembers.presentation P).encode ⊤ = top := SetMembers.raw_ofMem top topMem
  have dataEq : data = M.refinementLevelFormulaData e (SetMembers.presentation P) b d
      level T T2 system.valid1 := by
    have equal := M.rawRefinementFormulaData_eq e (SetMembers.presentation P) t b d
      pairing unions powers separation collection carrier group nodes supports
      system.inputs.condition_maps level T T2 system.valid1 system.valid2
    have carrierEq : (SetMembers.presentation P).carrier = P := rfl
    simpa only [carrierEq, orderLaw.conditionOrder_eq, topEq, graph] using equal
  have typedBelow : ZFSet.pair q p ∈ (SetMembers.presentation P).conditionOrder := by
    rw [orderLaw.conditionOrder_eq]
    exact below
  rw [dataEq] at tests ⊢
  exact M.refinementLevelRawTests_order_mono e (SetMembers.presentation P) b d level
    pairing unions powers separation collection carrier nextOrder nodes hT
    system.valid1 system.indices base directed system.first A tests typedBelow

end PartitionPilot.Forcing.RawRefinementStageWitness



namespace PartitionPilot.Forcing.RawRefinementStageWitness
open SetRealization SetFormula
universe u
variable {G L : Type u} [Group G] [PartialOrder L]
variable {M : TransitiveGround.{u}} {t : Presentation G} {b : Presentation L}
variable {d : PosetAction G L} {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}
variable (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : P ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (groundOrder : order ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets)
local notation "data" => M.rawRefinementFormulaData P order top action
  t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
include witness pairing unions powers separation collection carrier group nodes groundOrder supports hT

theorem rawTests_union (family rows : Nat → ZFSet.{u}) (q : ZFSet.{u})
    (increasing : ∀ n m, n ≤ m → family n ⊆ family m)
    (below : ∀ n, ZFSet.pair q (rows n) ∈ data 8)
    (tests : ∀ n, stageOneRawTests M data (family n) (rows n)) :
    stageOneRawTests M data (stageOneAssignmentUnion family) q := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  have topEq : (SetMembers.presentation P).encode ⊤ = top := SetMembers.raw_ofMem top topMem
  have dataEq : data = M.refinementLevelFormulaData e (SetMembers.presentation P) b d
      level T T2 system.valid1 := by
    have equal := M.rawRefinementFormulaData_eq e (SetMembers.presentation P) t b d
      pairing unions powers separation collection carrier group nodes supports
      system.inputs.condition_maps level T T2 system.valid1 system.valid2
    have carrierEq : (SetMembers.presentation P).carrier = P := rfl
    simpa only [carrierEq, orderLaw.conditionOrder_eq, topEq, graph] using equal
  have bounds (n : Nat) : q ∈ P ∧ rows n ∈ P := ZFSet.pair_mem_prod.1 (orderLaw.relation (below n))
  let lower : SetMembers P := SetMembers.ofMem q (bounds 0).1
  let sequence : Nat → SetMembers P := fun n => SetMembers.ofMem (rows n) (bounds n).2
  have lowerCode : (SetMembers.presentation P).encode lower = q := SetMembers.raw_ofMem _ _
  have sequenceCode (n : Nat) : (SetMembers.presentation P).encode (sequence n) = rows n := SetMembers.raw_ofMem _ _
  have meaning := M.refinementLevelRawTests_iff e (SetMembers.presentation P) b d level
    pairing unions powers separation collection carrier nextOrder nodes hT system.valid1
    system.indices base directed system.first
  rw [dataEq] at tests ⊢
  rw [← lowerCode]
  apply (meaning _ lower).2
  apply M.refinementLevelTests_union (SetMembers.presentation P) pairing unions powers separation
    collection carrier nextOrder hT system.valid1 e b d base directed system.first
    level T2 family sequence lower increasing
  · intro n
    change ZFSet.pair ((SetMembers.presentation P).encode lower)
      ((SetMembers.presentation P).encode (sequence n)) ∈ order
    rw [lowerCode, sequenceCode]
    exact below n
  · intro n
    apply (meaning (family n) (sequence n)).1
    rw [sequenceCode]
    exact tests n

end PartitionPilot.Forcing.RawRefinementStageWitness



namespace PartitionPilot.Forcing.RawRefinementStageWitness
open SetRealization SetFormula
universe u
variable {G L : Type u} [Group G] [PartialOrder L]
variable {M : TransitiveGround.{u}} {t : Presentation G} {b : Presentation L}
variable {d : PosetAction G L} {base : L} {directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z}
variable {T T2 level P order top action : ZFSet.{u}}
variable (witness : RawRefinementStageWitness M t b d base directed T T2 level P order top action)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : P ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (groundOrder : order ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
local notation "data" => M.rawRefinementFormulaData P order top action
  t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
local notation "branch" => fun g => M.rawStageRefinementAssignmentActionGraph (t.encode g)
  P order top action t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 level
include witness pairing unions powers separation collection carrier group nodes groundOrder supports hLevel hT

theorem relationLaws : RelationActionLaws G (stageOneAssignments (data 0) T) branch := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  have topEq : (SetMembers.presentation P).encode ⊤ = top := SetMembers.raw_ofMem top topMem
  have laws := M.rawStageRefinement_relationLaws e (SetMembers.presentation P) t b d
    pairing unions powers separation collection carrier group nodes nextOrder supports
    level T T2 system.valid1 system.valid2 system.inputs hLevel hT system.indices.index_ground
  have carrierEq : (SetMembers.presentation P).carrier = P := rfl
  simpa only [carrierEq, orderLaw.conditionOrder_eq, topEq, graph] using laws

theorem assignment_function (g : G) :
    ZFSet.IsFunc (stageOneAssignments (data 0) T) (stageOneAssignments (data 0) T) (branch g) :=
  (witness.relationLaws pairing unions powers separation collection carrier group nodes
    groundOrder supports hLevel hT).function g

theorem rawTests_actionGraph_iff (g : G) (A p q : ZFSet.{u})
    (edge : ZFSet.pair (ZFSet.pair (t.encode g) p) q ∈ action) :
    stageOneRawTests M data (relationImage A (stageOneAssignments (data 0) T) (branch g)) q ↔
      stageOneRawTests M data A p := by
  obtain ⟨orderLaw, topMem, greatest, e, graph, system⟩ := witness
  let := orderLaw.toPartialOrder
  let := orderLaw.toOrderTop top topMem greatest
  have nextOrder : (SetMembers.presentation P).conditionOrder ∈ M.sets := by
    rw [orderLaw.conditionOrder_eq]
    exact groundOrder
  have topEq : (SetMembers.presentation P).encode ⊤ = top := SetMembers.raw_ofMem top topMem
  have typedEdge : ZFSet.pair (ZFSet.pair (t.encode g) p) q ∈ e.actionGraph (SetMembers.presentation P) t :=
    graph.symm ▸ edge
  have tests := M.rawStageRefinementTests_actionGraph_iff e (SetMembers.presentation P) t b d
    pairing unions powers separation collection carrier group nodes nextOrder supports
    level T T2 system.valid1 system.valid2 system.inputs hLevel hT system.indices.index_ground
    system.indices base directed system.first g A p q typedEdge
  have carrierEq : (SetMembers.presentation P).carrier = P := rfl
  simpa only [carrierEq, orderLaw.conditionOrder_eq, topEq, graph] using tests

end PartitionPilot.Forcing.RawRefinementStageWitness

end OAI
