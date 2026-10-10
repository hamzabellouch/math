import OAI.RingTheory.DirectFiniteness.CandidateModel

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A]

lemma card_le_of_unique_cover {α : Type u_5} {β : Type u_6} [Fintype α] [Fintype β]
    (Rel : α → β → Prop) (hex : ∀ a, ∃ b, Rel a b)
    (hunique : ∀ a a' b, Rel a b → Rel a' b → a=a') : Fintype.card α ≤ Fintype.card β := by
  choose f hf using hex
  apply Fintype.card_le_of_injective f
  intro a a' h
  exact hunique a a' (f a) (hf a) (h ▸ hf a')

lemma pair_set_of_card_two {I : Type u_7} [DecidableEq I] {s : Finset I}
    (hcard : s.card = 2) {i : I} (hi : i ∈ s) : ∃ a, a ≠ i ∧ s = {i,a} := by
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hcard
  rw [hs] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨b,hab.symm,hs⟩
  · exact ⟨a,hab,by rw [hs,Finset.pair_comm]⟩

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)
variable (j : R × Q) (C : AffineCoset (F.U j))

structure Rooted where
  cycle : Candidate F T k
  root : Fin k
  label_eq : (cycle.step root).label = .inl j
  point_mem : cycle.point root ∈ C.val

namespace Rooted
@[ext] lemma ext {c d : Rooted F T k j C} (hc : c.cycle = d.cycle) (hr : c.root = d.root) : c=d := by
  cases c; cases d; cases hc; cases hr; rfl
instance [Fintype Q] [Fintype R] [Fintype E] : Fintype (Rooted F T k j C) :=
  Fintype.ofInjective (fun c => (c.cycle,c.root)) (by
    intro c d h
    exact ext F T k j C (congrArg Prod.fst h) (congrArg Prod.snd h))
end Rooted

/-- A deliberately generous finite codec. The last field stores k exceptional
scalars rather than just one; the final numeric load still tends to zero. -/
structure TwoCode where
  other : R × Q
  idx : Fin 4 → Fin k
  tag : Fin k → Fin 3
  point : C.val
  vec0 : Q × E
  vec1 : Q × E
  exc : Fin k → Q

instance [Fintype Q] [Fintype R] [Fintype E] : Fintype (TwoCode F k j C) :=
  Fintype.ofInjective (fun c => (c.other,c.idx,c.tag,c.point,c.vec0,c.vec1,c.exc)) (by
    rintro ⟨a,b,c,d,e,f,g⟩ ⟨a',b',c',d',e',f',g'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := h
    rfl)

def TwoCode.lab (z : TwoCode F k j C) (i : Fin k) : (R × Q) ⊕ R :=
  ![.inl j,.inl z.other,.inr j.1] (z.tag i)

def TwoCode.known (z : TwoCode F k j C) (i : Fin k) : A :=
  if i=z.idx 0 then F.u j z.vec0 else
    if i=z.idx 2 then F.u z.other z.vec1 else F.exc j.1 (z.exc i)

structure CoveredTwo (c : Rooted F T k j C) (z : TwoCode F k j C) : Prop where
  other_ne : j ≠ z.other
  root_eq : c.root = z.idx 0
  lab : ∀ i, (c.cycle.step i).label = z.lab F k j C i
  omit0 : (c.cycle.step (z.idx 1)).label = .inl j
  omit1 : (c.cycle.step (z.idx 3)).label = .inl z.other
  point : c.cycle.point (z.idx 0) = z.point.val
  known : ∀ i, i ≠ z.idx 1 → i ≠ z.idx 3 → (c.cycle.step i).vector F = z.known F k j C i

lemma CoveredTwo.unique {c d : Rooted F T k j C} {z : TwoCode F k j C}
    (hc : CoveredTwo F T k j C c z) (hd : CoveredTwo F T k j C d z) : c=d := by
  have hab : z.idx 1 ≠ z.idx 3 := by
    intro h
    exact hc.other_ne (Sum.inl.inj (hc.omit0.symm.trans (h ▸ hc.omit1)))
  have hv : (fun i => (c.cycle.step i).vector F) = fun i => (d.cycle.step i).vector F := by
    apply two_position_recovery (F.U j) (F.U z.other) (F.U_disjoint hc.other_ne)
      (z.idx 1) (z.idx 3) hab
    · exact F.vector_mem_U hc.omit0
    · exact F.vector_mem_U hd.omit0
    · exact F.vector_mem_U hc.omit1
    · exact F.vector_mem_U hd.omit1
    · exact c.cycle.closed F T
    · exact d.cycle.closed F T
    · intro i hi hi'
      exact (hc.known i hi hi').trans (hd.known i hi hi').symm
  have hs : c.cycle.step = d.cycle.step := by
    funext i
    exact PolygonStep.eq_of_label_vector_eq F ((hc.lab i).trans (hd.lab i).symm) (congrFun hv i)
  have hp := Candidate.points_eq F T c.cycle d.cycle hs (z.idx 0) (hc.point.trans hd.point.symm)
  exact Rooted.ext F T k j C (Candidate.ext F T hs hp) (hc.root_eq.trans hd.root_eq.symm)

lemma two_label_codec (c : Rooted F T k j C) (hk : k ≤ 5)
    (hg : c.cycle.labels.card = 2) : ∃ z : TwoCode F k j C, CoveredTwo F T k j C c z := by
  have hj : j ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨c.root,c.label_eq⟩
  obtain ⟨j',hj'ne,hlabels⟩ := pair_set_of_card_two hg hj
  have hj' : j' ∈ c.cycle.labels := by rw [hlabels]; simp
  have hrmem : c.root ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j) := by
    simp [c.label_eq]
  obtain ⟨a,har,hgen0⟩ := pair_set_of_card_two (c.cycle.count_eq_two F T hk j hj) hrmem
  obtain ⟨b,hb⟩ := (mem_genericLabels _ _).mp hj'
  have hbmem : b ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j') := by simp [hb]
  obtain ⟨d,hdb,hgen1⟩ := pair_set_of_card_two (c.cycle.count_eq_two F T hk j' hj') hbmem
  have hother : j ≠ j' := hj'ne.symm
  have hgeneric (i : Fin k) (g : GenericStep Q R E) (hi : c.cycle.step i = .inl g) :
      g.label = j ∨ g.label = j' := by
    have hh : g.label ∈ c.cycle.labels := (mem_genericLabels _ _).mpr ⟨i,by rw [hi]; rfl⟩
    rw [hlabels] at hh
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hexceptional (i : Fin k) (e : ExceptionalStep Q R) (hi : c.cycle.step i = .inr e) :
      e.label = j.1 := by
    have hh := F.two_generic_bundle c.cycle.step hk (c.cycle.closed F T) c.cycle.adjacent hg
      e.label ⟨i,by rw [hi]; rfl⟩
    exact (hh.2 j hj).symm
  let coords (step : PolygonStep Q R E) : Q × E :=
    Sum.elim (fun generic => (generic.scalar,generic.component)) (fun _ => 0) step
  let tag (index : Fin k) : Fin 3 :=
    Sum.elim (fun generic => if generic.label = j then 0 else 1) (fun _ => 2) (c.cycle.step index)
  let exc (index : Fin k) : Q :=
    Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (c.cycle.step index)
  let z : TwoCode F k j C := ⟨j',![c.root,a,b,d],tag,
    ⟨c.cycle.point c.root,c.point_mem⟩,coords (c.cycle.step c.root),coords (c.cycle.step b),exc⟩
  have hgen0' (i : Fin k) : (c.cycle.step i).label = .inl j ↔ i=c.root ∨ i=a := by
    have hh : i ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j) ↔ i ∈ ({c.root,a} : Finset (Fin k)) := by rw [hgen0]
    simpa using hh
  have hgen1' (i : Fin k) : (c.cycle.step i).label = .inl j' ↔ i=b ∨ i=d := by
    have hh : i ∈ Finset.univ.filter (fun i => (c.cycle.step i).label = .inl j') ↔ i ∈ ({b,d} : Finset (Fin k)) := by rw [hgen1]
    simpa using hh
  have hcoord (i : Fin k) (l : R × Q) (hi : (c.cycle.step i).label = .inl l) :
      (c.cycle.step i).vector F = F.u l (coords (c.cycle.step i)) := by
    cases he : c.cycle.step i with
    | inl g =>
      rw [he] at hi
      have hh := Sum.inl.inj hi
      cases hh
      rfl
    | inr e => simp [he,PolygonStep.label] at hi
  refine ⟨z,hother,rfl,?_,(hgen0' a).mpr (Or.inr rfl),(hgen1' d).mpr (Or.inr rfl),rfl,?_⟩
  · intro i
    cases hi : c.cycle.step i with
    | inl g =>
      rcases hgeneric i g hi with hg | hg
      · simp [z,TwoCode.lab,tag,hi,PolygonStep.label,hg]
      · simp [z,TwoCode.lab,tag,hi,PolygonStep.label,hg,hj'ne]
    | inr e => simp [z,TwoCode.lab,tag,hi,PolygonStep.label,hexceptional i e hi]
  · intro i hia hid
    change i ≠ a at hia
    change i ≠ d at hid
    change _ = if i=c.root then F.u j (coords (c.cycle.step c.root)) else
      if i=b then F.u j' (coords (c.cycle.step b)) else F.exc j.1 (exc i)
    by_cases hir : i=c.root
    · subst i; rw [ite_eq_left rfl]; exact hcoord c.root j c.label_eq
    rw [ite_eq_right hir]
    by_cases hib : i=b
    · subst i; rw [ite_eq_left rfl]; exact hcoord b j' hb
    rw [ite_eq_right hib]
    cases hi : c.cycle.step i with
    | inl g =>
      rcases hgeneric i g hi with hg | hg
      · have hh := (hgen0' i).mp (by rw [hi]; exact congrArg Sum.inl hg)
        exact False.elim (hh.elim hir hia)
      · have hh := (hgen1' i).mp (by rw [hi]; exact congrArg Sum.inl hg)
        exact False.elim (hh.elim hib hid)
    | inr e => simp [PolygonStep.vector,exc,hi,hexceptional i e hi]

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
