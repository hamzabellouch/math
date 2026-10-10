import OAI.SetTheory.PartitionPrinciple.Transfinite.RecursiveLiftAgreement

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

structure SetActionCode (G X m e A : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc (ZFSet.prod G X) X A
  one : ∀ p ∈ X, ZFSet.pair (ZFSet.pair e p) p ∈ A
  mul : ∀ g ∈ G, ∀ h ∈ G, ∀ k ∈ G, ∀ p ∈ X, ∀ q ∈ X, ∀ r ∈ X,
    ZFSet.pair (ZFSet.pair g h) k ∈ m → ZFSet.pair (ZFSet.pair h p) q ∈ A →
    ZFSet.pair (ZFSet.pair g q) r ∈ A → ZFSet.pair (ZFSet.pair k p) r ∈ A

theorem PosetActionCode.toSetAction {G P m e r A : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) : SetActionCode G P m e A :=
  ⟨action.function, action.one, action.mul⟩

noncomputable def taggedActionGraph (G P N A B : ZFSet.{u}) : ZFSet.{u} :=
  A ∪ ZFSet.sep (fun z => ∃ g ∈ G, ∃ q ∈ N, ∃ t ∈ N,
    z = ZFSet.pair (ZFSet.pair g (ZFSet.pair P q)) (ZFSet.pair P t) ∧
      ZFSet.pair (ZFSet.pair g q) t ∈ B)
    (ZFSet.prod (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N))

theorem triple_mem_taggedActionGraph (G P N A B g x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈ taggedActionGraph G P N A B ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A ∨
        (g ∈ G ∧ ∃ q ∈ N, ∃ t ∈ N, x = ZFSet.pair P q ∧ y = ZFSet.pair P t ∧
          ZFSet.pair (ZFSet.pair g q) t ∈ B) := by
  rw [taggedActionGraph, ZFSet.mem_union, ZFSet.mem_sep]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨_, g', hg, q, hq, t, ht, equal, entry⟩
    obtain ⟨first, last⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨actor, middle⟩ := ZFSet.pair_inj.1 first
    subst g'
    exact ⟨hg, q, hq, t, ht, middle, last, entry⟩
  · rintro ⟨hg, q, hq, t, ht, rfl, rfl, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2
      ⟨hg, pair_mem_taggedExtension.2 hq⟩, pair_mem_taggedExtension.2 ht⟩,
      g, hg, q, hq, t, ht, rfl, entry⟩

theorem SetActionCode.entry_shape {G X m e A g x y : ZFSet.{u}}
    (action : SetActionCode G X m e A) (entry : ZFSet.pair (ZFSet.pair g x) y ∈ A) :
    g ∈ G ∧ x ∈ X ∧ y ∈ X := by
  have shape := ZFSet.pair_mem_prod.1 (action.function.1 entry)
  have domain := ZFSet.pair_mem_prod.1 shape.1
  exact ⟨domain.1, domain.2, shape.2⟩

theorem SetActionCode.entry_unique {G X m e A g x y z : ZFSet.{u}}
    (action : SetActionCode G X m e A)
    (first : ZFSet.pair (ZFSet.pair g x) y ∈ A)
    (second : ZFSet.pair (ZFSet.pair g x) z ∈ A) : y = z := by
  have shape := action.entry_shape first
  obtain ⟨w, _, unique⟩ := action.function.2 (ZFSet.pair g x)
    (ZFSet.pair_mem_prod.2 ⟨shape.1, shape.2.1⟩)
  exact (unique y first).trans (unique z second).symm

theorem taggedActionGraph_old_iff {G P N A B g x y : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair (ZFSet.pair g x) y ∈ taggedActionGraph G P N A B ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  rw [triple_mem_taggedActionGraph]
  refine ⟨fun h => h.elim id ?_, Or.inl⟩
  rintro ⟨_, q, _, t, _, equal, _, _⟩
  exact False.elim (pair_tag_not_mem P q (equal ▸ hx))

theorem taggedActionGraph_fresh_iff {G P N m e A B g q y : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair P q)) y ∈ taggedActionGraph G P N A B ↔
      ∃ t ∈ N, y = ZFSet.pair P t ∧ ZFSet.pair (ZFSet.pair g q) t ∈ B := by
  rw [triple_mem_taggedActionGraph]
  constructor
  · rintro (entry | ⟨_, q', _, t, ht, equal, hy, entry⟩)
    · exact False.elim (pair_tag_not_mem P q (old.entry_shape entry).2.1)
    · have same := (ZFSet.pair_inj.1 equal).2
      subst q'
      exact ⟨t, ht, hy, entry⟩
  · rintro ⟨t, ht, hy, entry⟩
    have shape := fresh.entry_shape entry
    exact Or.inr ⟨shape.1, q, shape.2.1, t, ht, rfl, hy, entry⟩

theorem taggedActionGraph_fresh_pair_iff {G P N m e A B g q t : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair P q)) (ZFSet.pair P t) ∈
      taggedActionGraph G P N A B ↔ ZFSet.pair (ZFSet.pair g q) t ∈ B := by
  rw [taggedActionGraph_fresh_iff old fresh]
  constructor
  · rintro ⟨t', _, equal, entry⟩
    exact (ZFSet.pair_inj.1 equal).2.symm ▸ entry
  · intro entry
    exact ⟨t, (fresh.entry_shape entry).2.2, rfl, entry⟩

theorem taggedActionGraph_subset {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) :
    taggedActionGraph G P N A B ⊆
      ZFSet.prod (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N) := by
  intro z hz
  rcases ZFSet.mem_union.1 hz with oldEntry | freshEntry
  · obtain ⟨v, hv, y, hy, rfl⟩ := ZFSet.mem_prod.1 (old.function.1 oldEntry)
    obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hv
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2
      ⟨hg, old_mem_taggedExtension hx⟩, old_mem_taggedExtension hy⟩
  · exact (ZFSet.mem_sep.1 freshEntry).1

theorem taggedActionGraph_function {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ZFSet.IsFunc (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N)
      (taggedActionGraph G P N A B) := by
  refine ⟨taggedActionGraph_subset old, ?_⟩
  intro v hv
  obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hv
  rcases mem_taggedExtension.1 hx with hx | ⟨q, hq, rfl⟩
  · obtain ⟨y, entry, unique⟩ := old.function.2 (ZFSet.pair g x) (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
    exact ⟨y, taggedActionGraph_old_iff hx |>.2 entry,
      fun z hz => unique z ((taggedActionGraph_old_iff hx).1 hz)⟩
  · obtain ⟨t, entry, unique⟩ := fresh.function.2 (ZFSet.pair g q) (ZFSet.pair_mem_prod.2 ⟨hg, hq⟩)
    refine ⟨ZFSet.pair P t, (taggedActionGraph_fresh_pair_iff old fresh).2 entry, ?_⟩
    intro y hy
    obtain ⟨t', _, equal, entry'⟩ := (taggedActionGraph_fresh_iff old fresh).1 hy
    exact equal.trans (congrArg (ZFSet.pair P) (unique t' entry'))

theorem taggedActionGraph_one {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ∀ x ∈ taggedExtension P N, ZFSet.pair (ZFSet.pair e x) x ∈ taggedActionGraph G P N A B := by
  intro x hx
  rcases mem_taggedExtension.1 hx with hx | ⟨q, hq, rfl⟩
  · exact (taggedActionGraph_old_iff hx).2 (old.one x hx)
  · exact (taggedActionGraph_fresh_pair_iff old fresh).2 (fresh.one q hq)

theorem taggedActionGraph_mul {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ∀ g ∈ G, ∀ h ∈ G, ∀ k ∈ G, ∀ p ∈ taggedExtension P N,
      ∀ q ∈ taggedExtension P N, ∀ s ∈ taggedExtension P N,
        ZFSet.pair (ZFSet.pair g h) k ∈ m →
        ZFSet.pair (ZFSet.pair h p) q ∈ taggedActionGraph G P N A B →
        ZFSet.pair (ZFSet.pair g q) s ∈ taggedActionGraph G P N A B →
        ZFSet.pair (ZFSet.pair k p) s ∈ taggedActionGraph G P N A B := by
  intro g hg h hh k hk p hp q _ s _ product first second
  rcases mem_taggedExtension.1 hp with hp | ⟨x, hx, rfl⟩
  · have first' := (taggedActionGraph_old_iff hp).1 first
    have hq := (old.entry_shape first').2.2
    have second' := (taggedActionGraph_old_iff hq).1 second
    have hs := (old.entry_shape second').2.2
    exact (taggedActionGraph_old_iff hp).2 (old.mul g hg h hh k hk p hp q hq s hs product first' second')
  · obtain ⟨y, hy, rfl, first'⟩ := (taggedActionGraph_fresh_iff old fresh).1 first
    obtain ⟨z, hz, rfl, second'⟩ := (taggedActionGraph_fresh_iff old fresh).1 second
    exact (taggedActionGraph_fresh_pair_iff old fresh).2
      (fresh.mul g hg h hh k hk x hx y hy z hz product first' second')

theorem SetActionCode.tagged {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    SetActionCode G (taggedExtension P N) m e (taggedActionGraph G P N A B) :=
  ⟨taggedActionGraph_function old fresh, taggedActionGraph_one old fresh, taggedActionGraph_mul old fresh⟩

end

namespace SetActionCode

open SetRealization
universe u
variable {G X m inv one A : ZFSet.{u}}
variable (action : SetActionCode G X m one A)

noncomputable def rawAct (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ X}) : {x : ZFSet.{u} // x ∈ X} :=
  let graph : FunctionGraphOn (ZFSet.prod G X) A := ⟨X, action.function⟩
  let input := (⟨ZFSet.pair g.val x.val, ZFSet.pair_mem_prod.2 ⟨g.property, x.property⟩⟩ :
    {z : ZFSet.{u} // z ∈ ZFSet.prod G X})
  ⟨graph.value input, (ZFSet.pair_mem_prod.1 (action.function.1 (graph.value_entry input))).2⟩

theorem rawAct_entry (g : {g : ZFSet.{u} // g ∈ G}) (x : {x : ZFSet.{u} // x ∈ X}) :
    ZFSet.pair (ZFSet.pair g.val x.val) (action.rawAct g x).val ∈ A :=
  (show FunctionGraphOn (ZFSet.prod G X) A from ⟨X, action.function⟩).value_entry
    ⟨ZFSet.pair g.val x.val, ZFSet.pair_mem_prod.2 ⟨g.property, x.property⟩⟩

theorem rawAct_eq_iff (g : {g : ZFSet.{u} // g ∈ G})
    (x y : {x : ZFSet.{u} // x ∈ X}) :
    action.rawAct g x = y ↔ ZFSet.pair (ZFSet.pair g.val x.val) y.val ∈ A := by
  constructor
  · intro equal
    exact equal ▸ action.rawAct_entry g x
  · intro entry
    exact Subtype.ext (action.entry_unique (action.rawAct_entry g x) entry)

noncomputable def inverseActor (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) : {g : ZFSet.{u} // g ∈ G} :=
  ⟨SetMembers.raw (group.inv (SetMembers.ofMem g.val g.property)),
    SetMembers.raw_mem _⟩

theorem inverseActor_left (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) :
    ZFSet.pair (ZFSet.pair (inverseActor group g).val g.val) one ∈ m := by
  apply group.inv_mul g.val g.property _ (inverseActor group g).property
  simpa only [inverseActor, SetMembers.raw_ofMem] using
    group.inv_mem (SetMembers.ofMem g.val g.property)

theorem inverseActor_right (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) :
    ZFSet.pair (ZFSet.pair g.val (inverseActor group g).val) one ∈ m := by
  let actor := SetMembers.ofMem g.val g.property
  have equal : group.mul actor (group.inv actor) = group.one := by
    let := group.toGroup
    exact mul_inv_cancel actor
  have entry := group.mul_mem actor (group.inv actor)
  rw [equal, group.raw_one] at entry
  simpa only [actor, inverseActor, SetMembers.raw_ofMem] using entry

theorem rawAct_inverse_left (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) (x : {x : ZFSet.{u} // x ∈ X}) :
    action.rawAct (inverseActor group g) (action.rawAct g x) = x := by
  apply Subtype.ext
  exact action.entry_unique
    (action.mul _ (inverseActor group g).property g.val g.property one group.identity_mem
      x.val x.property _ (action.rawAct g x).property _
      (action.rawAct (inverseActor group g) (action.rawAct g x)).property
      (inverseActor_left group g) (action.rawAct_entry g x)
      (action.rawAct_entry (inverseActor group g) (action.rawAct g x)))
    (action.one x.val x.property)

theorem rawAct_inverse_right (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) (x : {x : ZFSet.{u} // x ∈ X}) :
    action.rawAct g (action.rawAct (inverseActor group g) x) = x := by
  apply Subtype.ext
  exact action.entry_unique
    (action.mul g.val g.property _ (inverseActor group g).property one group.identity_mem
      x.val x.property _ (action.rawAct (inverseActor group g) x).property _
      (action.rawAct g (action.rawAct (inverseActor group g) x)).property
      (inverseActor_right group g) (action.rawAct_entry (inverseActor group g) x)
      (action.rawAct_entry g (action.rawAct (inverseActor group g) x)))
    (action.one x.val x.property)

noncomputable def toPerm (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) : Equiv.Perm {x : ZFSet.{u} // x ∈ X} where
  toFun := action.rawAct g
  invFun := action.rawAct (inverseActor group g)
  left_inv := action.rawAct_inverse_left group g
  right_inv := action.rawAct_inverse_right group g

end SetActionCode

section

universe u

namespace BoundedFormula

open SetFormula

def taggedActionEntryFormula {n} (z G P N B : Fin n) : BoundedFormula n :=
  exMem G (exMem N.succ (exMem N.succ.succ
    (.conj (nestedActionTripleFormula z.succ.succ.succ 2 P.succ.succ.succ 1 P.succ.succ.succ 0)
      (tripleMembershipFormula 2 1 0 B.succ.succ.succ))))

theorem truth_taggedActionEntryFormula {n} (z G P N B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taggedActionEntryFormula z G P N B) env ↔
      ∃ g ∈ env G, ∃ q ∈ env N, ∃ t ∈ env N,
        env z = ZFSet.pair (ZFSet.pair g (ZFSet.pair (env P) q)) (ZFSet.pair (env P) t) ∧
          ZFSet.pair (ZFSet.pair g q) t ∈ env B := by
  simp only [taggedActionEntryFormula, truth_exMem, Truth,
    truth_nestedActionTripleFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem taggedActionGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G P N A B : ZFSet.{u}} (hG : G ∈ M.sets) (hP : P ∈ M.sets)
    (hN : N ∈ M.sets) (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    taggedActionGraph G P N A B ∈ M.sets := by
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  let params := extend G (extend P (extend N (extend B Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.taggedActionEntryFormula 0 1 2 3 4) params
    (Fin.cases hG (Fin.cases hP (Fin.cases hN (Fin.cases hB (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG hL) hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.taggedActionEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N)) =
      ZFSet.sep (fun z => ∃ g ∈ G, ∃ q ∈ N, ∃ t ∈ N,
        z = ZFSet.pair (ZFSet.pair g (ZFSet.pair P q)) (ZFSet.pair P t) ∧
          ZFSet.pair (ZFSet.pair g q) t ∈ B)
        (ZFSet.prod (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N)) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taggedActionEntryFormula 0 1 2 3 4 _)
  exact M.binary_union_mem pairing unions hA (equal ▸ selected)

end TransitiveGround

structure CodedAttachmentCovariance (G P N A B inside shadow upper : ZFSet.{u}) : Prop where
  inside : ∀ g ∈ G, ∀ q ∈ N, ∀ t ∈ N, ∀ q' ∈ N, ∀ t' ∈ N,
    ZFSet.pair (ZFSet.pair g q) q' ∈ B → ZFSet.pair (ZFSet.pair g t) t' ∈ B →
    ZFSet.pair q t ∈ inside → ZFSet.pair q' t' ∈ inside
  shadow : ∀ g ∈ G, ∀ q ∈ N, ∀ q' ∈ N, ∀ p ∈ P, ∀ p' ∈ P,
    ZFSet.pair (ZFSet.pair g q) q' ∈ B → ZFSet.pair (ZFSet.pair g p) p' ∈ A →
    ZFSet.pair q p ∈ shadow → ZFSet.pair q' p' ∈ shadow
  upper : ∀ g ∈ G, ∀ q ∈ N, ∀ q' ∈ N, ∀ p ∈ P, ∀ p' ∈ P,
    ZFSet.pair (ZFSet.pair g q) q' ∈ B → ZFSet.pair (ZFSet.pair g p) p' ∈ A →
    ZFSet.pair q p ∈ upper → ZFSet.pair q' p' ∈ upper

theorem CodedAttachmentCovariance.monotone
    {G P N m e r A B inside shadow upper : ZFSet.{u}}
    (covariance : CodedAttachmentCovariance G P N A B inside shadow upper)
    (old : PosetActionCode G P m e r A) (fresh : SetActionCode G N m e B) :
    ∀ g ∈ G, ∀ p ∈ taggedExtension P N, ∀ q ∈ taggedExtension P N,
      ∀ p' ∈ taggedExtension P N, ∀ q' ∈ taggedExtension P N,
        ZFSet.pair (ZFSet.pair g p) p' ∈ taggedActionGraph G P N A B →
        ZFSet.pair (ZFSet.pair g q) q' ∈ taggedActionGraph G P N A B →
        ZFSet.pair p q ∈ codedAttachmentOrder P N r inside shadow upper →
        ZFSet.pair p' q' ∈ codedAttachmentOrder P N r inside shadow upper := by
  intro g hg p _ q _ p' hp' q' hq' first second lower
  have compared := ((pair_mem_codedAttachmentOrder P N r inside shadow upper p q).1 lower).2.2
  apply (pair_mem_codedAttachmentOrder P N r inside shadow upper p' q').2
  refine ⟨hp', hq', ?_⟩
  rcases compared with oldOld | oldFresh | freshOld | freshFresh
  · obtain ⟨hp, hq, below⟩ := oldOld
    have actedP := (taggedActionGraph_old_iff hp).1 first
    have actedQ := (taggedActionGraph_old_iff hq).1 second
    have hp'P := (old.toSetAction.entry_shape actedP).2.2
    have hq'P := (old.toSetAction.entry_shape actedQ).2.2
    exact Or.inl ⟨hp'P, hq'P, old.monotone g hg p hp q hq p' hp'P q' hq'P actedP actedQ below⟩
  · obtain ⟨hp, t, ht, s, hs, rfl, shadowEntry, below⟩ := oldFresh
    have actedP := (taggedActionGraph_old_iff hp).1 first
    have hp'P := (old.toSetAction.entry_shape actedP).2.2
    obtain ⟨t', ht', rfl, actedT⟩ := (taggedActionGraph_fresh_iff old.toSetAction fresh).1 second
    obtain ⟨s', actedS, _⟩ := old.function.2 (ZFSet.pair g s) (ZFSet.pair_mem_prod.2 ⟨hg, hs⟩)
    have hs' := (old.toSetAction.entry_shape actedS).2.2
    exact Or.inr (Or.inl ⟨hp'P, t', ht', s', hs', rfl,
      covariance.shadow g hg t ht t' ht' s hs s' hs' actedT actedS shadowEntry,
      old.monotone g hg p hp s hs p' hp'P s' hs' actedP actedS below⟩)
  · obtain ⟨hq, t, ht, rfl, upperEntry⟩ := freshOld
    obtain ⟨t', ht', rfl, actedT⟩ := (taggedActionGraph_fresh_iff old.toSetAction fresh).1 first
    have actedQ := (taggedActionGraph_old_iff hq).1 second
    have hq'P := (old.toSetAction.entry_shape actedQ).2.2
    exact Or.inr (Or.inr (Or.inl ⟨hq'P, t', ht', rfl,
      covariance.upper g hg t ht t' ht' q hq q' hq'P actedT actedQ upperEntry⟩))
  · obtain ⟨s, hs, t, ht, rfl, rfl, below⟩ := freshFresh
    obtain ⟨s', hs', rfl, actedS⟩ := (taggedActionGraph_fresh_iff old.toSetAction fresh).1 first
    obtain ⟨t', ht', rfl, actedT⟩ := (taggedActionGraph_fresh_iff old.toSetAction fresh).1 second
    refine Or.inr (Or.inr (Or.inr ⟨s', hs', t', ht', rfl, rfl, ?_⟩))
    rcases below with internal | ⟨v, hv, shadowEntry, upperEntry⟩
    · exact Or.inl (covariance.inside g hg s hs t ht s' hs' t' ht' actedS actedT internal)
    · obtain ⟨v', actedV, _⟩ := old.function.2 (ZFSet.pair g v) (ZFSet.pair_mem_prod.2 ⟨hg, hv⟩)
      have hv' := (old.toSetAction.entry_shape actedV).2.2
      exact Or.inr ⟨v', hv',
        covariance.shadow g hg t ht t' ht' v hv v' hv' actedT actedV shadowEntry,
        covariance.upper g hg s hs s' hs' v hv v' hv' actedS actedV upperEntry⟩

theorem PosetActionCode.tagged_attachment
    {G P N m e r A B inside shadow upper : ZFSet.{u}}
    (old : PosetActionCode G P m e r A) (fresh : SetActionCode G N m e B)
    (covariance : CodedAttachmentCovariance G P N A B inside shadow upper) :
    PosetActionCode G (taggedExtension P N) m e
      (codedAttachmentOrder P N r inside shadow upper) (taggedActionGraph G P N A B) :=
  ⟨(old.toSetAction.tagged fresh).function, (old.toSetAction.tagged fresh).one,
    (old.toSetAction.tagged fresh).mul, covariance.monotone old fresh⟩

end

open Compression.RecursiveMaps
universe u

structure CodedRecursiveTaskAction
    {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
    {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
    (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
    (T : ZFSet.{u}) : Prop where
  taskAction : SetActionCode G I m one T
  source : ∀ g i j a b, ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair i a ∈ Sources → ZFSet.pair j b ∈ Sources → a = b
  intertwine : ∀ g i j S S' p x y, ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair i S ∈ Maps → ZFSet.pair j S' ∈ Maps →
    ZFSet.pair p x ∈ S → ZFSet.pair p y ∈ S' → ZFSet.pair (ZFSet.pair g x) y ∈ A

namespace CodedRecursiveTaskAction

variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)

noncomputable def current (_s : CodedRecursiveTaskAction h T) (g : {g : ZFSet.{u} // g ∈ G}) :
    Compression.MeetIso d.templates.extension d.templates.extension := by
  let encoding := d.coding.encodingIso
  let acted := h.action.toMeetIso h.group d.batch_meetOrder g
  refine isoOfOrder
    (fun x => encoding.inverse (acted.toFun (encoding.toFun x)))
    (fun x => encoding.inverse (acted.inverse (encoding.toFun x))) ?_ ?_ ?_
  · intro x
    rw [encoding.right_inverse, acted.left_inverse, encoding.left_inverse]
  · intro x
    rw [encoding.right_inverse, acted.right_inverse, encoding.left_inverse]
  · intro x y
    exact ((inverseIso encoding).le_iff _ _).trans
      ((acted.le_iff _ _).trans (encoding.le_iff x y))

theorem current_entry (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair g.val (d.coding.encode x))
      (d.coding.encode ((s.current g).toFun x)) ∈ A := by
  change ZFSet.pair (ZFSet.pair g.val (d.coding.encode x))
    (d.coding.encode (d.coding.decode ((h.action.toMeetIso h.group d.batch_meetOrder g).toFun
      ⟨d.coding.encode x, d.coding.encode_mem x⟩))) ∈ A
  rw [d.coding.encode_decode]
  exact h.action.toMeetIso_entry h.group d.batch_meetOrder g
    ⟨d.coding.encode x, d.coding.encode_mem x⟩

noncomputable def toTaskSymmetry (g : {g : ZFSet.{u} // g ∈ G}) : TaskSymmetry h.toInputs where
  perm := s.taskAction.rawAct g
  inverse := (s.taskAction.toPerm h.group g).invFun
  left_inverse := (s.taskAction.toPerm h.group g).left_inv
  right_inverse := (s.taskAction.toPerm h.group g).right_inv
  current := s.current g
  source i := Subtype.ext (s.source g.val i.val _ _ _ (s.taskAction.rawAct_entry g i)
    (h.source_entry i) (h.source_entry (s.taskAction.rawAct g i))).symm
  intertwine i p := by
    apply d.coding.encode_injective
    exact h.action.toSetAction.entry_unique (s.current_entry g ((h.toInputs.previous i).toFun p))
      (s.intertwine g.val i.val _ _ _ p.val _ _ (s.taskAction.rawAct_entry g i)
        (h.maps.value_entry i) (h.maps.value_entry (s.taskAction.rawAct g i))
        (h.toInputs_previous_entry i p) (h.toInputs_previous_entry (s.taskAction.rawAct g i) p))

theorem toTaskSymmetry_perm_entry (g : {g : ZFSet.{u} // g ∈ G})
    (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.pair (ZFSet.pair g.val i.val) ((s.toTaskSymmetry g).perm i).val ∈ T :=
  s.taskAction.rawAct_entry g i

theorem toTaskSymmetry_current_entry (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair g.val (d.coding.encode x))
      (d.coding.encode ((s.toTaskSymmetry g).current.toFun x)) ∈ A := s.current_entry g x

end CodedRecursiveTaskAction

end PartitionPilot.Forcing

end OAI
