import OAI.SetTheory.PartitionPrinciple.Definability.TaskTransportFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.CodedRecursiveTaskActions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundEligibleCaps
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundHeightPushforward

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem taskTransportGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G I P R U Labels A : ZFSet.{u}} (hG : G ∈ M.sets) (hI : I ∈ M.sets)
    (hP : P ∈ M.sets) (hR : R ∈ M.sets) (hU : U ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hA : A ∈ M.sets) :
    taskTransportGraph G I P R U Labels A ∈ M.sets := by
  let params := extend G (extend I (extend P (extend R (extend U (extend Labels (extend A Fin.elim0))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.taskTransportEntryFormula 0 1 2 3 4 5 6 7) params
    (Fin.cases hG (Fin.cases hI (Fin.cases hP (Fin.cases hR (Fin.cases hU
      (Fin.cases hLabels (Fin.cases hA (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG hI) hI)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.taskTransportEntryFormula 0 1 2 3 4 5 6 7) (extend z params))
      (ZFSet.prod (ZFSet.prod G I) I) = taskTransportGraph G I P R U Labels A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, taskTransportGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taskTransportEntryFormula 0 1 2 3 4 5 6 7 _)
  exact equal ▸ selected

noncomputable def groundTaskTransport (P G r μ A Labels : ZFSet.{u}) : ZFSet.{u} :=
  taskTransportGraph G (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels A

theorem literalTask_transport_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e a c base s F label δ c' s' : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hδ : δ ∈ G)
    (ht : literalTaskCode a c base s F label ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair (ZFSet.pair δ c) c' ∈ A)
    (separator : ZFSet.pair (ZFSet.pair δ s) s' ∈ A) :
    literalTaskCode a c' (actionPostcompose P A δ base) s' (actionImage P A δ F) label ∈
      M.groundEligibleTasks P G r μ A Labels := by
  have old := (M.literalTaskCode_mem_groundEligibleTasks P G r μ A Labels a c base s F label).1 ht
  exact (M.literalTaskCode_mem_groundEligibleTasks P G r μ A Labels a c'
    (actionPostcompose P A δ base) s' (actionImage P A δ F) label).2
    ⟨old.1, M.actionPostcompose_mem pairing unions powers separation hP hA (M.transitive hG hδ) old.2.1,
      M.actionImage_mem separation hP hA (M.transitive hG hδ) old.2.2.1,
      old.2.2.2.transport group action meet hδ target separator⟩

theorem groundTaskTransport_total
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    ∀ δ ∈ G, ∀ t ∈ M.groundEligibleTasks P G r μ A Labels,
      ∃ t' ∈ M.groundEligibleTasks P G r μ A Labels,
        TaskTransportCode P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels A δ t t' := by
  intro δ hδ t ht
  obtain ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel, equal, _⟩ :=
    (mem_eligibleTaskSet P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels t).1 ht
  subst t
  obtain ⟨c', target, _⟩ := action.function.2 (ZFSet.pair δ c) (ZFSet.pair_mem_prod.2 ⟨hδ, hc⟩)
  obtain ⟨s', separator, _⟩ := action.function.2 (ZFSet.pair δ s) (ZFSet.pair_mem_prod.2 ⟨hδ, hs⟩)
  have newTask := M.literalTask_transport_mem pairing unions powers separation hP hG hA
    group action meet hδ ht target separator
  have fields := (literalTaskCode_mem_eligibleTaskSet P G r μ A
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels a c'
    (actionPostcompose P A δ base) s' (actionImage P A δ F) label).1 newTask
  exact ⟨_, newTask, a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel,
    c', fields.2.1, actionPostcompose P A δ base, fields.2.2.1,
    s', fields.2.2.2.1, actionImage P A δ F, fields.2.2.2.2.1,
    rfl, rfl, target, separator, rfl, rfl⟩

theorem groundTaskTransport_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    ZFSet.IsFunc (ZFSet.prod G (M.groundEligibleTasks P G r μ A Labels))
      (M.groundEligibleTasks P G r μ A Labels) (M.groundTaskTransport P G r μ A Labels) :=
  taskTransportGraph_function action
    (M.groundTaskTransport_total pairing unions powers separation hP hG hA group action meet)

theorem groundTaskTransport_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (meet : MeetOrderCode P r μ) :
    M.groundTaskTransport P G r μ A Labels ∈ M.sets :=
  M.taskTransportGraph_mem pairing unions powers separation hG
    (M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet)
    hP (M.groundRelations_mem pairing unions powers separation hP hP)
    (M.groundMeetFilters_mem powers separation hP hr hμ meet) hLabels hA

theorem groundTaskTransport_one {P G r μ A Labels m e : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (he : e ∈ G) :
    ∀ t ∈ M.groundEligibleTasks P G r μ A Labels,
      ZFSet.pair (ZFSet.pair e t) t ∈ M.groundTaskTransport P G r μ A Labels :=
  taskTransportGraph_one action he
    (fun base hbase => ((M.mem_groundRelations P P base).1 hbase).2)
    (fun F hF => ((M.mem_groundMeetFilters P r μ F).1 hF).2.subset)
    (eligibleTaskSet_subset P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)

theorem groundTaskTransport_mul {P G r μ A Labels m e g h k t t' t'' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m)
    (first : ZFSet.pair (ZFSet.pair h t) t' ∈ M.groundTaskTransport P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair g t') t'' ∈ M.groundTaskTransport P G r μ A Labels) :
    ZFSet.pair (ZFSet.pair k t) t'' ∈ M.groundTaskTransport P G r μ A Labels :=
  taskTransportGraph_mul action
    (fun F hF => ((M.mem_groundMeetFilters P r μ F).1 hF).2.subset) hg hh hk product first second

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

noncomputable def indexedTaskActionGraph (G I P N T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ i ∈ I, ∃ j ∈ I, ∃ q ∈ P,
    z = ZFSet.pair (ZFSet.pair g (ZFSet.pair i q)) (ZFSet.pair j q) ∧
      ZFSet.pair (ZFSet.pair g i) j ∈ T)
    (ZFSet.prod (ZFSet.prod G N) N)

theorem indexedTaskActionGraph_subset (G I P N T : ZFSet.{u}) :
    indexedTaskActionGraph G I P N T ⊆ ZFSet.prod (ZFSet.prod G N) N :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_indexedTaskActionGraph (G I P N T z : ZFSet.{u}) :
    z ∈ indexedTaskActionGraph G I P N T ↔
      ∃ g ∈ G, ∃ i ∈ I, ∃ j ∈ I, ∃ q ∈ P,
        ZFSet.pair i q ∈ N ∧ ZFSet.pair j q ∈ N ∧
        z = ZFSet.pair (ZFSet.pair g (ZFSet.pair i q)) (ZFSet.pair j q) ∧
          ZFSet.pair (ZFSet.pair g i) j ∈ T := by
  constructor
  · intro hz
    obtain ⟨bound, g, hg, i, hi, j, hj, q, hq, rfl, entry⟩ := ZFSet.mem_sep.1 hz
    have outer := ZFSet.pair_mem_prod.1 bound
    exact ⟨g, hg, i, hi, j, hj, q, hq, (ZFSet.pair_mem_prod.1 outer.1).2,
      outer.2, rfl, entry⟩
  · rintro ⟨g, hg, i, hi, j, hj, q, hq, source, target, rfl, entry⟩
    exact ZFSet.mem_sep.2
      ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, source⟩, target⟩,
        g, hg, i, hi, j, hj, q, hq, rfl, entry⟩

theorem triple_mem_indexedTaskActionGraph (G I P N T g x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈ indexedTaskActionGraph G I P N T ↔
      g ∈ G ∧ x ∈ N ∧ y ∈ N ∧ ∃ i ∈ I, ∃ j ∈ I, ∃ q ∈ P,
        x = ZFSet.pair i q ∧ y = ZFSet.pair j q ∧ ZFSet.pair (ZFSet.pair g i) j ∈ T := by
  rw [mem_indexedTaskActionGraph]
  constructor
  · rintro ⟨a, ha, i, hi, j, hj, q, hq, source, target, equal, entry⟩
    obtain ⟨first, last⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨actor, middle⟩ := ZFSet.pair_inj.1 first
    subst a x y
    exact ⟨ha, source, target, i, hi, j, hj, q, hq, rfl, rfl, entry⟩
  · rintro ⟨hg, source, target, i, hi, j, hj, q, hq, rfl, rfl, entry⟩
    exact ⟨g, hg, i, hi, j, hj, q, hq, source, target, rfl, entry⟩

theorem indexedTaskActionGraph_entry_iff (G I P N T g i j q q' : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair i q)) (ZFSet.pair j q') ∈
      indexedTaskActionGraph G I P N T ↔
      g ∈ G ∧ i ∈ I ∧ j ∈ I ∧ q ∈ P ∧ q' = q ∧
        ZFSet.pair i q ∈ N ∧ ZFSet.pair j q ∈ N ∧ ZFSet.pair (ZFSet.pair g i) j ∈ T := by
  rw [triple_mem_indexedTaskActionGraph]
  constructor
  · rintro ⟨hg, source, target, a, ha, b, hb, t, ht, first, second, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
    exact ⟨hg, ha, hb, ht, rfl, source, target, entry⟩
  · rintro ⟨hg, hi, hj, hq, rfl, source, target, entry⟩
    exact ⟨hg, source, target, i, hi, j, hj, _, hq, rfl, rfl, entry⟩

theorem indexedTaskActionGraph_function {G I P N T : ZFSet.{u}}
    (task : ZFSet.IsFunc (ZFSet.prod G I) I T) (shape : N ⊆ ZFSet.prod I P)
    (closed : ∀ g ∈ G, ∀ i ∈ I, ∀ j ∈ I, ∀ q ∈ P,
      ZFSet.pair i q ∈ N → ZFSet.pair (ZFSet.pair g i) j ∈ T → ZFSet.pair j q ∈ N) :
    ZFSet.IsFunc (ZFSet.prod G N) N (indexedTaskActionGraph G I P N T) := by
  refine ⟨indexedTaskActionGraph_subset G I P N T, ?_⟩
  intro v hv
  obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hv
  obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
  obtain ⟨j, entry, unique⟩ := task.2 (ZFSet.pair g i) (ZFSet.pair_mem_prod.2 ⟨hg, hi⟩)
  have hj := (ZFSet.pair_mem_prod.1 (task.1 entry)).2
  refine ⟨ZFSet.pair j q, (indexedTaskActionGraph_entry_iff G I P N T g i j q q).2
    ⟨hg, hi, hj, hq, rfl, hx, closed g hg i hi j hj q hq hx entry, entry⟩, ?_⟩
  intro y hy
  obtain ⟨_, _, _, a, _, b, _, t, _, first, second, other⟩ :=
    (triple_mem_indexedTaskActionGraph G I P N T g (ZFSet.pair i q) y).1 hy
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
  exact second.trans (congrArg (fun k => ZFSet.pair k q) (unique b other))

theorem indexedTaskActionGraph_setAction {G I P N T m e : ZFSet.{u}}
    (task : SetActionCode G I m e T) (shape : N ⊆ ZFSet.prod I P)
    (closed : ∀ g ∈ G, ∀ i ∈ I, ∀ j ∈ I, ∀ q ∈ P,
      ZFSet.pair i q ∈ N → ZFSet.pair (ZFSet.pair g i) j ∈ T → ZFSet.pair j q ∈ N) :
    SetActionCode G N m e (indexedTaskActionGraph G I P N T) := by
  refine ⟨indexedTaskActionGraph_function task.function shape closed, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    have identity := task.one i hi
    have he := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (task.function.1 identity)).1).1
    exact (indexedTaskActionGraph_entry_iff G I P N T e i i q q).2
      ⟨he, hi, hi, hq, rfl, hx, hx, identity⟩
  · intro g hg h hh k hk x hx y hy z hz product first second
    obtain ⟨_, _, _, i, hi, j, hj, q, hq, xEq, yEq, firstTask⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T h x y).1 first
    obtain ⟨_, _, _, j', hj', l, hl, q', hq', yEq', zEq, secondTask⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g y z).1 second
    have equal := ZFSet.pair_inj.1 (yEq.symm.trans yEq')
    obtain ⟨rfl, rfl⟩ := equal
    exact (triple_mem_indexedTaskActionGraph G I P N T k x z).2
      ⟨hk, hx, hz, i, hi, l, hl, _, hq, xEq, zEq,
        task.mul g hg h hh k hk i hi _ hj l hl product firstTask secondTask⟩

theorem constantTemplateFresh_subset (I P r anchors : ZFSet.{u}) :
    indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r) anchors ⊆
      ZFSet.prod I P := by
  intro z hz
  obtain ⟨i, hi, q, rfl, Q, r', a, space, _, _, hq, _⟩ :=
    (mem_indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r) anchors z).1 hz
  have equal := ((pair_mem_constantFamilyGraph I P i Q).1 space).2
  exact ZFSet.pair_mem_prod.2 ⟨hi, equal ▸ hq⟩

namespace TransitiveGround

open SetFormula

noncomputable def groundEligibleFreshAction (M : TransitiveGround.{u})
    (P G r μ A Labels : ZFSet.{u}) : ZFSet.{u} :=
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
    (literalTaskSourceGraph I P R U Labels)
  indexedTaskActionGraph G I P N (M.groundTaskTransport P G r μ A Labels)

theorem groundTaskTransport_setAction (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    SetActionCode G (M.groundEligibleTasks P G r μ A Labels) m e
      (M.groundTaskTransport P G r μ A Labels) := by
  refine ⟨M.groundTaskTransport_function pairing unions powers separation hP hG hA group action meet,
    M.groundTaskTransport_one action group.identity_mem, ?_⟩
  intro g hg h hh k hk _ _ _ _ _ _ product first second
  exact M.groundTaskTransport_mul action hg hh hk product first second

theorem groundEligibleFreshAction_setAction (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels)
    SetActionCode G N m e (M.groundEligibleFreshAction P G r μ A Labels) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  apply indexedTaskActionGraph_setAction
    (M.groundTaskTransport_setAction pairing unions powers separation hP hG hA group action meet)
    (constantTemplateFresh_subset I P r (literalTaskSourceGraph I P R U Labels))
  intro g _ i hi j hj q _ fresh entry
  have transported := ((triple_mem_taskTransportGraph G I P R U Labels A g i j).1 entry).2.2.2
  exact (transported.fresh_iff hi hj).1 fresh

end TransitiveGround






def ActionAgreementBelow (P r A g h v : ZFSet.{u}) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x v ∈ r →
    (ZFSet.pair (ZFSet.pair g x) y ∈ A ↔ ZFSet.pair (ZFSet.pair h x) y ∈ A)

namespace ActionAgreementBelow

variable {P r A g h v : ZFSet.{u}}
variable (agree : ActionAgreementBelow P r A g h v)
include agree

theorem symm : ActionAgreementBelow P r A h g v :=
  fun x hx y hy lower => (agree x hx y hy lower).symm

theorem entry_eq {G m e x y z : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hh : h ∈ G) (hx : x ∈ P)
    (lower : ZFSet.pair x v ∈ r)
    (first : ZFSet.pair (ZFSet.pair g x) y ∈ A)
    (second : ZFSet.pair (ZFSet.pair h x) z ∈ A) : y = z := by
  have hy := (ZFSet.pair_mem_prod.1 (action.function.1 first)).2
  have shared := (agree x hx y hy lower).1 first
  obtain ⟨w, _, unique⟩ := action.function.2 (ZFSet.pair h x) (ZFSet.pair_mem_prod.2 ⟨hh, hx⟩)
  exact (unique y shared).trans (unique z second).symm

theorem image_subset {G m inv e μ F : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hh : h ∈ G)
    (filter : MeetFilterCode P r μ F) (positive : v ∈ F) :
    actionImage P A g F ⊆ actionImage P A h F := by
  intro y hy
  obtain ⟨hyP, x, hx, image⟩ := (mem_actionImage P A g F y).1 hy
  obtain ⟨w, entry, _⟩ := meet.operation.2 (ZFSet.pair x v)
    (ZFSet.pair_mem_prod.2 ⟨filter.subset hx, filter.subset positive⟩)
  have hwF := filter.closed_meet x hx v positive w entry
  have hwP := filter.subset hwF
  obtain ⟨z, shared, _⟩ := action.function.2 (ZFSet.pair g w) (ZFSet.pair_mem_prod.2 ⟨hg, hwP⟩)
  have hzP := (ZFSet.pair_mem_prod.1 (action.function.1 shared)).2
  have shared' := (agree w hwP z hzP (meet.lower_right x v w entry)).1 shared
  have hzF : z ∈ actionImage P A h F := (mem_actionImage P A h F z).2 ⟨hzP, w, hwF, shared'⟩
  have lower := action.monotone g hg w hwP x (filter.subset hx) z hzP y hyP
    shared image (meet.lower_left x v w entry)
  exact (actionImage_filter group action meet hh filter).upward z hzF y hyP lower

theorem actionImage_eq {G m inv e μ F : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hh : h ∈ G)
    (filter : MeetFilterCode P r μ F) (positive : v ∈ F) :
    actionImage P A g F = actionImage P A h F := by
  apply ZFSet.ext
  intro y
  exact ⟨fun hy => agree.image_subset group action meet hg hh filter positive hy,
    fun hy => agree.symm.image_subset group action meet hh hg filter positive hy⟩

theorem postcompose_eq {base : ZFSet.{u}}
    (bound : ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x y ∈ base → ZFSet.pair y v ∈ r) :
    actionPostcompose P A g base = actionPostcompose P A h base := by
  have inclusion {b c : ZFSet.{u}} (same : ActionAgreementBelow P r A b c v) :
      actionPostcompose P A b base ⊆ actionPostcompose P A c base := by
    intro z hz
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (actionPostcompose_subset P A b base hz)
    obtain ⟨hx, hy, w, hw, entry, acted⟩ := (pair_mem_actionPostcompose P A b base x y).1 hz
    exact (pair_mem_actionPostcompose P A c base x y).2
      ⟨hx, hy, w, hw, entry, (same w hw y hy (bound x hx w hw entry)).1 acted⟩
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => inclusion agree hz, fun hz => inclusion agree.symm hz⟩

end ActionAgreementBelow

theorem EligibleTaskCode.base_below_positive
    {P G r μ A source target base separator F m e v x y : ZFSet.{u}}
    (code : EligibleTaskCode P G r μ A source target base separator F)
    (action : PosetActionCode G P m e r A) (order : PartialOrderCode P r)
    (positive : v ∈ F) (entry : ZFSet.pair x y ∈ base) : ZFSet.pair y v ∈ r := by
  obtain ⟨k, hk, represented⟩ := code.representative
  have shape := ZFSet.pair_mem_prod.1 (represented.shape entry)
  have lower := (represented.entries x shape.1 y shape.2).1 entry
  have yt := action.monotone k hk x shape.1 source code.source_mem y shape.2 target code.target_mem
    lower.2 represented.target_entry lower.1
  exact order.trans y shape.2 separator code.separator_mem v (code.filter.subset positive)
    (order.trans y shape.2 target code.target_mem separator code.separator_mem yt code.lower)
    (code.upper v positive)

theorem TaskTransportCode.literal_outputs
    {P R U Labels A g a c base s F label t' : ZFSet.{u}}
    (transport : TaskTransportCode P R U Labels A g (literalTaskCode a c base s F label) t') :
    ∃ c' ∈ P, ∃ base' ∈ R, ∃ s' ∈ P, ∃ F' ∈ U,
      t' = literalTaskCode a c' base' s' F' label ∧
      ZFSet.pair (ZFSet.pair g c) c' ∈ A ∧ ZFSet.pair (ZFSet.pair g s) s' ∈ A ∧
      base' = actionPostcompose P A g base ∧ F' = actionImage P A g F := by
  obtain ⟨a₀, _, c₀, _, b₀, _, s₀, _, F₀, _, l₀, _,
    c', hc', b', hb', s', hs', F', hF', old, new, target, separator, baseEq, filterEq⟩ := transport
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := literalTaskCode_inj.1 old
  exact ⟨c', hc', b', hb', s', hs', F', hF', new, target, separator, baseEq, filterEq⟩

theorem TaskTransportCode.positive_agreement
    {P G r μ A R U Labels m inv e g h v a c base s F label t' t'' : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hh : h ∈ G)
    (code : EligibleTaskCode P G r μ A a c base s F)
    (agree : ActionAgreementBelow P r A g h v) (positive : v ∈ F)
    (first : TaskTransportCode P R U Labels A g (literalTaskCode a c base s F label) t')
    (second : TaskTransportCode P R U Labels A h (literalTaskCode a c base s F label) t'') : t' = t'' := by
  obtain ⟨c', _, base', _, s', _, F', _, new, target, separator, baseEq, filterEq⟩ := first.literal_outputs
  obtain ⟨c'', _, base'', _, s'', _, F'', _, new', target', separator', baseEq', filterEq'⟩ := second.literal_outputs
  have sv := code.upper v positive
  have cv := meet.order.trans c code.target_mem s code.separator_mem v (code.filter.subset positive) code.lower sv
  have sameC := agree.entry_eq action hh code.target_mem cv target target'
  have sameS := agree.entry_eq action hh code.separator_mem sv separator separator'
  have sameBase : base' = base'' := baseEq.trans ((agree.postcompose_eq
    (fun _ _ _ _ entry => code.base_below_positive action meet.order positive entry)).trans baseEq'.symm)
  have sameFilter : F' = F'' := filterEq.trans
    ((agree.actionImage_eq group action meet hg hh code.filter positive).trans filterEq'.symm)
  rw [new, new', sameC, sameS, sameBase, sameFilter]

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem groundTaskTransport_positive_agreement
    {P G r μ A Labels m inv e g h v a c base s F label t' t'' : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (agree : ActionAgreementBelow P r A g h v) (positive : v ∈ F)
    (first : ZFSet.pair (ZFSet.pair g (literalTaskCode a c base s F label)) t' ∈
      M.groundTaskTransport P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair h (literalTaskCode a c base s F label)) t'' ∈
      M.groundTaskTransport P G r μ A Labels) : t' = t'' := by
  have parts := (triple_mem_taskTransportGraph G (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels A g _ t').1 first
  have parts' := (triple_mem_taskTransportGraph G (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels A h _ t'').1 second
  have code := ((M.literalTaskCode_mem_groundEligibleTasks P G r μ A Labels a c base s F label).1 parts.2.1).2.2.2
  exact TaskTransportCode.positive_agreement group action meet parts.1 parts'.1 code agree positive
    parts.2.2.2 parts'.2.2.2

end TransitiveGround






namespace BoundedFormula

open SetFormula

def indexedTaskActionEntryFormula {n} (z G I P T : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ
  exMem G (exMem I.succ (exMem I.succ.succ (exMem P.succ.succ.succ
    (.conj (nestedActionTripleFormula (lift z) 3 2 0 1 0)
      (tripleMembershipFormula 3 2 1 (lift T))))))

theorem truth_indexedTaskActionEntryFormula {n} (z G I P T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedTaskActionEntryFormula z G I P T) env ↔
      ∃ g ∈ env G, ∃ i ∈ env I, ∃ j ∈ env I, ∃ q ∈ env P,
        env z = ZFSet.pair (ZFSet.pair g (ZFSet.pair i q)) (ZFSet.pair j q) ∧
          ZFSet.pair (ZFSet.pair g i) j ∈ env T := by
  simp only [indexedTaskActionEntryFormula, truth_exMem, Truth,
    truth_nestedActionTripleFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem indexedTaskActionGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G I P N T : ZFSet.{u}} (hG : G ∈ M.sets) (hI : I ∈ M.sets)
    (hP : P ∈ M.sets) (hN : N ∈ M.sets) (hT : T ∈ M.sets) :
    indexedTaskActionGraph G I P N T ∈ M.sets := by
  let params := extend G (extend I (extend P (extend T Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedTaskActionEntryFormula 0 1 2 3 4) params
    (Fin.cases hG (Fin.cases hI (Fin.cases hP (Fin.cases hT (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG hN) hN)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedTaskActionEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod G N) N) = indexedTaskActionGraph G I P N T := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedTaskActionGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_indexedTaskActionEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

noncomputable abbrev nextFreshSet :=
  indexedAttachmentFresh h.nextIndices (pairSecondField I J h.nextIndices Qs)
    (pairSecondField I J h.nextIndices rs) (pairSecondField I J h.nextIndices As)

noncomputable def nextIndexAction (T : ZFSet.{u}) :=
  indexedTaskActionGraph G I J h.nextIndices T

noncomputable def nextFreshAction (T : ZFSet.{u}) :=
  indexedTaskActionGraph G h.nextIndices (familyPointBound Qs) h.nextFreshSet (h.nextIndexAction T)

noncomputable def nextActionGraph (T : ZFSet.{u}) :=
  taggedActionGraph G d.batchCarrier h.nextFreshSet A (h.nextFreshAction T)

theorem nextFreshSet_shape : h.nextFreshSet ⊆ ZFSet.prod h.nextIndices (familyPointBound Qs) := by
  intro z fresh
  obtain ⟨i, _, j, _, q, rfl, index, oldFresh⟩ := recursiveFresh_shape
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs) fresh
  have bounds := ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset J Qs
    (indexedAttachmentFresh_subset J Qs rs As oldFresh))
  exact ZFSet.pair_mem_prod.2 ⟨index, bounds.2⟩

variable {T : ZFSet.{u}} (task : SetActionCode G I m one T)
variable (sourceInvariant : ∀ g i j a b, ZFSet.pair (ZFSet.pair g i) j ∈ T →
  ZFSet.pair i a ∈ Sources → ZFSet.pair j b ∈ Sources → a = b)

include task sourceInvariant in
theorem nextIndices_closed {g i i' j : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair g i) i' ∈ T)
    (index : ZFSet.pair i j ∈ h.nextIndices) : ZFSet.pair i' j ∈ h.nextIndices := by
  have bounds := task.entry_shape entry
  have hj := (ZFSet.pair_mem_prod.1
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs index)).2
  let a := h.source ⟨i, bounds.2.1⟩
  let b := h.source ⟨i', bounds.2.2⟩
  let f := d.filter ⟨j, hj⟩
  have equal : a.val = b.val := sourceInvariant g i i' a.val b.val entry
    (h.source_entry ⟨i, bounds.2.1⟩) (h.source_entry ⟨i', bounds.2.2⟩)
  have negative : a.val ∉ f := (recursiveAttachmentIndices_entry_iff h.sources d.filters.to_isFunc
    (h.source_entry ⟨i, bounds.2.1⟩) (d.filter_entry ⟨j, hj⟩)).1 index
  exact (recursiveAttachmentIndices_entry_iff h.sources d.filters.to_isFunc
    (h.source_entry ⟨i', bounds.2.2⟩) (d.filter_entry ⟨j, hj⟩)).2 (equal ▸ negative)

include task sourceInvariant in
theorem nextIndexAction_setAction : SetActionCode G h.nextIndices m one (h.nextIndexAction T) :=
  indexedTaskActionGraph_setAction task
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs)
    (fun _ _ _ _ _ _ _ _ index entry => h.nextIndices_closed task sourceInvariant entry index)

include task sourceInvariant in
theorem nextFreshAction_setAction : SetActionCode G h.nextFreshSet m one (h.nextFreshAction T) := by
  apply indexedTaskActionGraph_setAction (h.nextIndexAction_setAction task sourceInvariant) h.nextFreshSet_shape
  intro g _ k _ k' hk' q _ fresh entry
  obtain ⟨_, _, _, i, hi, i', hi', j, hj, rfl, rfl, _⟩ :=
    (triple_mem_indexedTaskActionGraph G I J h.nextIndices T g k k').1 entry
  exact (recursiveFresh_iff hi' hj).2 ⟨hk', ((recursiveFresh_iff hi hj).1 fresh).2⟩

include task sourceInvariant in
theorem nextAction_setAction (M : TransitiveGround.{u}) (next : h.NextInputs M) :
    SetActionCode G next.batchCarrier m one (h.nextActionGraph T) :=
  h.action.toSetAction.tagged (h.nextFreshAction_setAction task sourceInvariant)

theorem nextAction_old_iff {g x y : ZFSet.{u}} (hx : x ∈ d.batchCarrier) :
    ZFSet.pair (ZFSet.pair g x) y ∈ h.nextActionGraph T ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A := taggedActionGraph_old_iff hx

include task sourceInvariant in
theorem nextAction_fresh_pair_iff {g q t : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair d.batchCarrier q)) (ZFSet.pair d.batchCarrier t) ∈
      h.nextActionGraph T ↔ ZFSet.pair (ZFSet.pair g q) t ∈ h.nextFreshAction T :=
  taggedActionGraph_fresh_pair_iff h.action.toSetAction (h.nextFreshAction_setAction task sourceInvariant)

include task in
theorem nextFreshAction_pair_iff {g i i' j q : ZFSet.{u}}
    (source : ZFSet.pair (ZFSet.pair i j) q ∈ h.nextFreshSet)
    (target : ZFSet.pair (ZFSet.pair i' j) q ∈ h.nextFreshSet) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair (ZFSet.pair i j) q))
      (ZFSet.pair (ZFSet.pair i' j) q) ∈ h.nextFreshAction T ↔
      ZFSet.pair (ZFSet.pair g i) i' ∈ T := by
  have sb := ZFSet.pair_mem_prod.1 (h.nextFreshSet_shape source)
  have tb := ZFSet.pair_mem_prod.1 (h.nextFreshSet_shape target)
  have si := ZFSet.pair_mem_prod.1
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs sb.1)
  have ti := ZFSet.pair_mem_prod.1
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs tb.1)
  rw [nextFreshAction, indexedTaskActionGraph_entry_iff, nextIndexAction,
    indexedTaskActionGraph_entry_iff]
  constructor
  · exact fun entry => entry.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · intro entry
    have hg := (task.entry_shape entry).1
    exact ⟨hg, sb.1, tb.1, sb.2, rfl, source, target,
      hg, si.1, ti.1, si.2, rfl, sb.1, tb.1, entry⟩

include task sourceInvariant in
theorem nextFreshSet_closed {g i i' j q : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair g i) i' ∈ T)
    (source : ZFSet.pair (ZFSet.pair i j) q ∈ h.nextFreshSet) :
    ZFSet.pair (ZFSet.pair i' j) q ∈ h.nextFreshSet := by
  have bounds := task.entry_shape entry
  have index := (ZFSet.pair_mem_prod.1 (h.nextFreshSet_shape source)).1
  have hj := (ZFSet.pair_mem_prod.1
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs index)).2
  exact (recursiveFresh_iff bounds.2.2 hj).2
    ⟨h.nextIndices_closed task sourceInvariant entry index,
      ((recursiveFresh_iff bounds.2.1 hj).1 source).2⟩

include task sourceInvariant in
theorem nextAction_fresh_entry {g i i' j q : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair g i) i' ∈ T)
    (source : ZFSet.pair (ZFSet.pair i j) q ∈ h.nextFreshSet) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair d.batchCarrier (ZFSet.pair (ZFSet.pair i j) q)))
      (ZFSet.pair d.batchCarrier (ZFSet.pair (ZFSet.pair i' j) q)) ∈ h.nextActionGraph T :=
  (h.nextAction_fresh_pair_iff task sourceInvariant).2
    ((h.nextFreshAction_pair_iff task source
      (h.nextFreshSet_closed task sourceInvariant entry source)).2 entry)

end PartitionPilot.Forcing.CodedRecursiveMapInputs



namespace PartitionPilot.Forcing.PosetActionCode
universe u
variable {G P m one r A g v : ZFSet.{u}}

theorem agreement_identity_iff_fixes (action : PosetActionCode G P m one r A) :
    ActionAgreementBelow P r A g one v ↔
      ∀ x ∈ P, ZFSet.pair x v ∈ r → ZFSet.pair (ZFSet.pair g x) x ∈ A := by
  constructor
  · intro agree x hx lower
    exact (agree x hx x hx lower).2 (action.one x hx)
  · intro fixes x hx y _ lower
    have fixed := fixes x hx lower
    have identity := action.one x hx
    have function : FunctionGraphOn (ZFSet.prod G P) A := ⟨P, action.function⟩
    exact ⟨fun entry => (function.unique entry fixed).symm ▸ identity,
      fun entry => (function.unique entry identity).symm ▸ fixed⟩

end PartitionPilot.Forcing.PosetActionCode



namespace PartitionPilot.Forcing.IdealEmbeddingCode
universe u
variable {P Q rP rQ μP μQ e G H mG mH oneG oneH A B : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
variable (source : PosetActionCode G P mG oneG rP A)
variable (target : PosetActionCode H Q mH oneH rQ B)
include code source target

theorem actionAgreementBelow {g h g' h' v v' : ZFSet.{u}}
    (hg : g ∈ G) (hg' : g' ∈ H) (hh' : h' ∈ H)
    (image : ZFSet.pair v v' ∈ e)
    (agree : ActionAgreementBelow P rP A g h v)
    (firstEquivariant : ∀ x ∈ P, ∀ y ∈ P, ∀ x' y',
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e →
      ZFSet.pair (ZFSet.pair g x) y ∈ A → ZFSet.pair (ZFSet.pair g' x') y' ∈ B)
    (secondEquivariant : ∀ x ∈ P, ∀ y ∈ P, ∀ x' y',
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e →
      ZFSet.pair (ZFSet.pair h x) y ∈ A → ZFSet.pair (ZFSet.pair h' x') y' ∈ B) :
    ActionAgreementBelow Q rQ B g' h' v' := by
  intro x' hx' z _ lower
  obtain ⟨x, hx, oldLower, xx'⟩ := code.ideal v v' x' image hx' lower
  obtain ⟨y, gy, _⟩ := source.function.2 (ZFSet.pair g x) (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
  have hy := (ZFSet.pair_mem_prod.1 (source.function.1 gy)).2
  have hyAct := (agree x hx y hy oldLower).1 gy
  obtain ⟨y', yy', _⟩ := code.injection.function.2 y hy
  have first := firstEquivariant x hx y hy x' y' xx' yy' gy
  have second := secondEquivariant x hx y hy x' y' xx' yy' hyAct
  obtain ⟨a, _, uniqueFirst⟩ := target.function.2 (ZFSet.pair g' x') (ZFSet.pair_mem_prod.2 ⟨hg', hx'⟩)
  obtain ⟨b, _, uniqueSecond⟩ := target.function.2 (ZFSet.pair h' x') (ZFSet.pair_mem_prod.2 ⟨hh', hx'⟩)
  constructor
  · intro entry
    have equal : z = y' := (uniqueFirst z entry).trans (uniqueFirst y' first).symm
    exact equal.symm ▸ second
  · intro entry
    have equal : z = y' := (uniqueSecond z entry).trans (uniqueSecond y' second).symm
    exact equal.symm ▸ first

end PartitionPilot.Forcing.IdealEmbeddingCode



namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u})

theorem nextIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets) : h.nextIndices ∈ M.sets :=
  M.recursiveAttachmentIndices_mem pairing unions powers separation hI hJ hD
    (M.union_mem unions (M.union_mem unions hFs)) hSources hFs

theorem nextFreshSet_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets) : h.nextFreshSet ∈ M.sets := by
  have hK := h.nextIndices_mem M pairing unions powers separation hI hJ hD hFs hSources
  have field : ∀ F ∈ M.sets, pairSecondField I J h.nextIndices F ∈ M.sets := by
    intro F hF
    exact M.pairFieldGraph_mem pairing unions powers separation false hI hJ hK
      (M.union_mem unions (M.union_mem unions hF)) hF
  exact M.indexedAttachmentFresh_mem pairing unions powers separation hK
    (field Qs hQs) (field rs hrs) (field As hAs)

theorem nextIndexAction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) : h.nextIndexAction T ∈ M.sets :=
  M.indexedTaskActionGraph_mem pairing unions powers separation hG hI hJ
    (h.nextIndices_mem M pairing unions powers separation hI hJ hD hFs hSources) hT

theorem nextFreshAction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) : h.nextFreshAction T ∈ M.sets :=
  M.indexedTaskActionGraph_mem pairing unions powers separation hG
    (h.nextIndices_mem M pairing unions powers separation hI hJ hD hFs hSources)
    (M.familyPointBound_mem unions hQs)
    (h.nextFreshSet_mem M pairing unions powers separation hI hJ hD hQs hrs hAs hFs hSources)
    (h.nextIndexAction_mem M pairing unions powers separation hI hJ hD hFs hSources hG hT)

theorem nextActionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : d.batchCarrier ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets)
    (hG : G ∈ M.sets) (hA : A ∈ M.sets) (hT : T ∈ M.sets) :
    h.nextActionGraph T ∈ M.sets :=
  M.taggedActionGraph_mem pairing unions powers separation hG hL
    (h.nextFreshSet_mem M pairing unions powers separation hI hJ hD hQs hrs hAs hFs hSources) hA
    (h.nextFreshAction_mem M pairing unions powers separation hI hJ hD hQs hrs hAs hFs hSources hG hT)

end PartitionPilot.Forcing.CodedRecursiveMapInputs

end OAI
