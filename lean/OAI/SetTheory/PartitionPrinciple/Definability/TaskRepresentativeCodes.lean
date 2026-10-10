import OAI.SetTheory.PartitionPrinciple.Forcing.ActionPostcompositionCodes

namespace OAI

namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula SetRealization
universe u

def actionSectionEntryFormula {n} (z g a p : Fin n) : BoundedFormula n :=
  exMem p (exMem p.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tripleMembershipFormula g.succ.succ 1 0 a.succ.succ)))

def actionSectionFormula {n} (f g a p : Fin n) : BoundedFormula n :=
  .conj (relationBetweenFormula p p f) (.allMem p (.allMem p.succ
    (.conj (imp (pairMembershipFormula 1 0 f.succ.succ)
      (tripleMembershipFormula g.succ.succ 1 0 a.succ.succ))
      (imp (tripleMembershipFormula g.succ.succ 1 0 a.succ.succ)
        (pairMembershipFormula 1 0 f.succ.succ)))))

theorem truth_actionSectionEntryFormula {n} (z g a p : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actionSectionEntryFormula z g a p) env ↔
      ∃ x ∈ env p, ∃ y ∈ env p, env z = ZFSet.pair x y ∧
        ZFSet.pair (ZFSet.pair (env g) x) y ∈ env a := by
  simp only [actionSectionEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

theorem truth_actionSectionFormula {n} (f g a p : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actionSectionFormula f g a p) env ↔
      env f ⊆ ZFSet.prod (env p) (env p) ∧ ∀ x ∈ env p, ∀ y ∈ env p,
        (ZFSet.pair x y ∈ env f ↔ ZFSet.pair (ZFSet.pair (env g) x) y ∈ env a) := by
  simp only [actionSectionFormula, Truth, truth_relationBetweenFormula, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ← iff_def]
  rfl

variable {G P : Type u} [Group G] [PartialOrder P]

theorem actionSectionEntry_correct (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (g : G) (z : ZFSet.{u}) :
    Truth (actionSectionEntryFormula 0 1 2 3)
      (extend z (extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) ↔
        z ∈ s.graph s (a.iso g) := by
  rw [truth_actionSectionEntryFormula]
  constructor
  · rintro ⟨x, hx, y, hy, eq, rel⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨q, rfl⟩ := (s.mem_carrier y).1 hy
    change z = ZFSet.pair (s.encode p) (s.encode q) at eq
    rw [eq, s.pair_mem_graph]
    exact (a.triple_mem_actionGraph s t g p q).1 rel
  · intro member
    obtain ⟨p, eq⟩ := (s.mem_graph s (a.iso g) z).1 member
    exact ⟨s.encode p, s.encode_mem p, s.encode (a.iso g p), s.encode_mem _, eq.symm,
      (a.triple_mem_actionGraph s t g p (a.iso g p)).2 rfl⟩

theorem actionSection_correct (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (g : G) (F : ZFSet.{u}) :
    Truth (actionSectionFormula 0 1 2 3)
      (extend F (extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) ↔
        F = s.graph s (a.iso g) := by
  rw [truth_actionSectionFormula]
  constructor
  · rintro ⟨shape, spec⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (shape hz)
      obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
      obtain ⟨q, rfl⟩ := (s.mem_carrier y).1 hy
      rw [eq, s.pair_mem_graph]
      exact (a.triple_mem_actionGraph s t g p q).1 ((spec _ hx _ hy).1 (eq ▸ hz))
    · intro hz
      obtain ⟨p, eq⟩ := (s.mem_graph s (a.iso g) z).1 hz
      exact eq ▸ (spec _ (s.encode_mem p) _ (s.encode_mem (a.iso g p))).2
        ((a.triple_mem_actionGraph s t g p (a.iso g p)).2 rfl)
  · intro eq
    subst F
    refine ⟨(s.graph_isFunc s (a.iso g)).1, ?_⟩
    intro x hx y hy
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨q, rfl⟩ := (s.mem_carrier y).1 hy
    exact (s.pair_mem_graph s (a.iso g) p q).trans (a.triple_mem_actionGraph s t g p q).symm

end BoundedFormula

namespace BoundedFormula

open SetFormula
universe u

def meetFilterFormula {n} (P r μ F : Fin n) : BoundedFormula n :=
  .conj (.allMem F (.mem 0 P.succ))
    (.conj (exMem F (.equal 0 0))
      (.conj
        (.allMem F (.allMem P.succ
          (imp (pairMembershipFormula 1 0 r.succ.succ) (.mem 0 F.succ.succ))))
        (.allMem F (.allMem F.succ (.allMem P.succ.succ
          (imp (tripleMembershipFormula 2 1 0 μ.succ.succ.succ)
            (.mem 0 F.succ.succ.succ)))))))

theorem truth_meetFilterFormula {n} (P r μ F : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (meetFilterFormula P r μ F) env ↔
      MeetFilterCode (env P) (env r) (env μ) (env F) := by
  simp only [meetFilterFormula, Truth, truth_exMem, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨subset, ⟨x, hx, _⟩, upward, closed⟩
    exact ⟨subset, ⟨x, hx⟩, upward, fun x hx y hy z entry =>
      closed x hx y hy z (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2 entry⟩
  · intro filter
    obtain ⟨x, hx⟩ := filter.nonempty
    exact ⟨filter.subset, ⟨x, hx, trivial⟩, filter.upward,
      fun x hx y hy z _ entry => filter.closed_meet x hx y hy z entry⟩

theorem realize_meetFilterFormula (M : TransitiveGround.{u}) {n}
    (P r μ F : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (meetFilterFormula P r μ F).toFormula env ↔
      MeetFilterCode (env P) (env r) (env μ) (env F) :=
  (realize_toFormula M _ env members).trans (truth_meetFilterFormula P r μ F env meet)

def restrictedActionEntryFormula {n} (z P r A g source : Fin n) : BoundedFormula n :=
  exMem P (exMem P.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (.conj (pairMembershipFormula 1 source.succ.succ r.succ.succ)
      (tripleMembershipFormula g.succ.succ 1 0 A.succ.succ))))

theorem truth_restrictedActionEntryFormula {n} (z P r A g source : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (restrictedActionEntryFormula z P r A g source) env ↔
      ∃ x ∈ env P, ∃ y ∈ env P, env z = ZFSet.pair x y ∧
        ZFSet.pair x (env source) ∈ env r ∧ ZFSet.pair (ZFSet.pair (env g) x) y ∈ env A := by
  simp only [restrictedActionEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

def restrictedActionFormula {n} (P r A g source target base : Fin n) : BoundedFormula n :=
  let entry := pairMembershipFormula 1 0 base.succ.succ
  let restricted := .conj (pairMembershipFormula 1 source.succ.succ r.succ.succ)
    (tripleMembershipFormula g.succ.succ 1 0 A.succ.succ)
  .conj (relationBetweenFormula P P base)
    (.conj (tripleMembershipFormula g source target A)
      (.allMem P (.allMem P.succ
        (.conj (imp entry restricted) (imp restricted entry)))))

theorem truth_restrictedActionFormula {n} (P r A g source target base : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (restrictedActionFormula P r A g source target base) env ↔
      RestrictedActionCode (env P) (env r) (env A) (env g) (env source) (env target) (env base) := by
  simp only [restrictedActionFormula, Truth, truth_relationBetweenFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_imp, ← iff_def]
  exact ⟨fun ⟨shape, target, entries⟩ => ⟨shape, target, entries⟩,
    fun code => ⟨code.shape, code.target_entry, code.entries⟩⟩

theorem realize_restrictedActionFormula (M : TransitiveGround.{u}) {n}
    (P r A g source target base : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (restrictedActionFormula P r A g source target base).toFormula env ↔
      RestrictedActionCode (env P) (env r) (env A) (env g) (env source) (env target) (env base) :=
  (realize_toFormula M _ env members).trans
    (truth_restrictedActionFormula P r A g source target base env)

end BoundedFormula

universe u

structure EligibleTaskCode (P G r μ A source target base separator F : ZFSet.{u}) : Prop where
  source_mem : source ∈ P
  target_mem : target ∈ P
  separator_mem : separator ∈ P
  filter : MeetFilterCode P r μ F
  lower : ZFSet.pair target separator ∈ r
  strict : ZFSet.pair separator target ∉ r
  upper : ∀ x ∈ F, ZFSet.pair separator x ∈ r
  representative : ∃ g ∈ G, RestrictedActionCode P r A g source target base

namespace BoundedFormula

open SetFormula

def eligibleTaskFormula {n} (P G r μ A source target base separator F : Fin n) : BoundedFormula n :=
  .conj (.mem source P) (.conj (.mem target P) (.conj (.mem separator P)
    (.conj (meetFilterFormula P r μ F) (.conj (pairMembershipFormula target separator r)
      (.conj (.neg (pairMembershipFormula separator target r))
        (.conj (allMem F (pairMembershipFormula separator.succ 0 r.succ))
          (exMem G (restrictedActionFormula P.succ r.succ A.succ 0
            source.succ target.succ base.succ))))))))

theorem truth_eligibleTaskFormula {n} (P G r μ A source target base separator F : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (eligibleTaskFormula P G r μ A source target base separator F) env ↔
      EligibleTaskCode (env P) (env G) (env r) (env μ) (env A)
        (env source) (env target) (env base) (env separator) (env F) := by
  simp only [eligibleTaskFormula, Truth, truth_pairMembershipFormula, truth_exMem,
    truth_restrictedActionFormula, truth_meetFilterFormula P r μ F env meet]
  constructor
  · rintro ⟨hs, ht, he, filter, lower, strict, upper, representative⟩
    exact ⟨hs, ht, he, filter, lower, strict, upper, representative⟩
  · intro code
    exact ⟨code.source_mem, code.target_mem, code.separator_mem, code.filter,
      code.lower, code.strict, code.upper, code.representative⟩

end BoundedFormula

noncomputable def eligibleTaskSet (P G r μ A R U Labels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ P, ∃ c ∈ P, ∃ base ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
    z = literalTaskCode a c base e F label ∧ EligibleTaskCode P G r μ A a c base e F)
    (literalTaskBound P R U Labels)

theorem eligibleTaskSet_subset (P G r μ A R U Labels : ZFSet.{u}) :
    eligibleTaskSet P G r μ A R U Labels ⊆ literalTaskBound P R U Labels :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_eligibleTaskSet (P G r μ A R U Labels z : ZFSet.{u}) :
    z ∈ eligibleTaskSet P G r μ A R U Labels ↔
      ∃ a ∈ P, ∃ c ∈ P, ∃ base ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
        z = literalTaskCode a c base e F label ∧ EligibleTaskCode P G r μ A a c base e F := by
  constructor
  · exact fun hz => (ZFSet.mem_sep.1 hz).2
  · rintro ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩
    exact ZFSet.mem_sep.2 ⟨(literalTaskCode_mem_bound P R U Labels a c base e F label).2
      ⟨ha, hc, hBase, he, hF, hLabel⟩,
      a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩

theorem literalTaskCode_mem_eligibleTaskSet (P G r μ A R U Labels a c base e F label : ZFSet.{u}) :
    literalTaskCode a c base e F label ∈ eligibleTaskSet P G r μ A R U Labels ↔
      a ∈ P ∧ c ∈ P ∧ base ∈ R ∧ e ∈ P ∧ F ∈ U ∧ label ∈ Labels ∧
        EligibleTaskCode P G r μ A a c base e F := by
  rw [mem_eligibleTaskSet]
  constructor
  · rintro ⟨a', ha, c', hc, base', hBase, e', he, F', hF, label', hLabel, equal, code⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := literalTaskCode_inj.1 equal
    exact ⟨ha, hc, hBase, he, hF, hLabel, code⟩
  · rintro ⟨ha, hc, hBase, he, hF, hLabel, code⟩
    exact ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩

namespace BoundedFormula

open SetFormula

def eligibleTaskEntryFormula {n} (z P G r μ A R U Labels : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  exMem P (exMem P.succ (exMem R.succ.succ (exMem P.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem Labels.succ.succ.succ.succ.succ
      (.conj (literalTaskFormula (lift z) 5 4 3 2 1 0)
        (eligibleTaskFormula (lift P) (lift G) (lift r) (lift μ) (lift A) 5 4 3 2 1)))))))

theorem truth_eligibleTaskEntryFormula {n} (z P G r μ A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (eligibleTaskEntryFormula z P G r μ A R U Labels) env ↔
      env z ∈ eligibleTaskSet (env P) (env G) (env r) (env μ) (env A) (env R) (env U) (env Labels) := by
  rw [mem_eligibleTaskSet]
  simp only [eligibleTaskEntryFormula, truth_exMem, Truth, truth_literalTaskFormula]
  refine exists_congr fun a => and_congr_right fun _ =>
    exists_congr fun c => and_congr_right fun _ =>
    exists_congr fun base => and_congr_right fun _ =>
    exists_congr fun e => and_congr_right fun _ =>
    exists_congr fun F => and_congr_right fun _ =>
    exists_congr fun label => and_congr_right fun _ => ?_
  exact and_congr Iff.rfl (truth_eligibleTaskFormula _ _ _ _ _ _ _ _ _ _
    (extend label (extend F (extend e (extend base (extend c (extend a env)))))) meet)

end BoundedFormula

def TaskRepresentative (P r A R U Labels task g : ZFSet.{u}) : Prop :=
  ∃ a ∈ P, ∃ c ∈ P, ∃ base ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
    task = literalTaskCode a c base e F label ∧ RestrictedActionCode P r A g a c base

theorem TaskRepresentative.restriction {P r A R U Labels g a c base e F label : ZFSet.{u}}
    (represented : TaskRepresentative P r A R U Labels (literalTaskCode a c base e F label) g) :
    RestrictedActionCode P r A g a c base := by
  obtain ⟨a', _, c', _, base', _, e', _, F', _, label', _, equal, code⟩ := represented
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := literalTaskCode_inj.1 equal
  exact code

noncomputable def taskRepresentativeRelation (I P G r A R U Labels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ task ∈ I, ∃ g ∈ G,
    z = ZFSet.pair task g ∧ TaskRepresentative P r A R U Labels task g) (ZFSet.prod I G)

theorem pair_mem_taskRepresentativeRelation (I P G r A R U Labels task g : ZFSet.{u}) :
    ZFSet.pair task g ∈ taskRepresentativeRelation I P G r A R U Labels ↔
      task ∈ I ∧ g ∈ G ∧ TaskRepresentative P r A R U Labels task g := by
  constructor
  · intro h
    obtain ⟨_, t, ht, h, hh, equal, represents⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ht, hh, represents⟩
  · rintro ⟨ht, hg, represents⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨ht, hg⟩, task, ht, g, hg, rfl, represents⟩

theorem eligibleTask_representative_total (P G r μ A R U Labels : ZFSet.{u}) :
    ∀ task ∈ eligibleTaskSet P G r μ A R U Labels, ∃ g ∈ G,
      ZFSet.pair task g ∈ taskRepresentativeRelation
        (eligibleTaskSet P G r μ A R U Labels) P G r A R U Labels := by
  intro task ht
  obtain ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, equal, code⟩ :=
    (mem_eligibleTaskSet P G r μ A R U Labels task).1 ht
  obtain ⟨g, hg, represents⟩ := code.representative
  exact ⟨g, hg, (pair_mem_taskRepresentativeRelation _ _ _ _ _ _ _ _ _ _).2
    ⟨ht, hg, a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, equal, represents⟩⟩

namespace BoundedFormula

open SetFormula

def taskRepresentativeFormula {n} (task g P r A R U Labels : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  exMem P (exMem P.succ (exMem R.succ.succ (exMem P.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem Labels.succ.succ.succ.succ.succ
      (.conj (literalTaskFormula (lift task) 5 4 3 2 1 0)
        (restrictedActionFormula (lift P) (lift r) (lift A) (lift g) 5 4 3)))))))

theorem truth_taskRepresentativeFormula {n} (task g P r A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskRepresentativeFormula task g P r A R U Labels) env ↔
      TaskRepresentative (env P) (env r) (env A) (env R) (env U) (env Labels) (env task) (env g) := by
  simp only [taskRepresentativeFormula, truth_exMem, Truth, truth_literalTaskFormula,
    truth_restrictedActionFormula, TaskRepresentative]
  rfl

def taskRepresentativeEntryFormula {n} (z I P G r A R U Labels : Fin n) : BoundedFormula n :=
  exMem I (exMem G.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (taskRepresentativeFormula 1 0 P.succ.succ r.succ.succ A.succ.succ
      R.succ.succ U.succ.succ Labels.succ.succ)))

theorem truth_taskRepresentativeEntryFormula {n} (z I P G r A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskRepresentativeEntryFormula z I P G r A R U Labels) env ↔
      ∃ task ∈ env I, ∃ g ∈ env G, env z = ZFSet.pair task g ∧
        TaskRepresentative (env P) (env r) (env A) (env R) (env U) (env Labels) task g := by
  simp only [taskRepresentativeEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_taskRepresentativeFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end OAI
