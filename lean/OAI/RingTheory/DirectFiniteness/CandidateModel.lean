import OAI.RingTheory.DirectFiniteness.CandidateGeometry

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

instance [Fintype Q] [Fintype R] [Fintype E] : Fintype (GenericStep Q R E) :=
  Fintype.ofInjective (fun g => (g.label,g.scalar,g.component)) (by
    rintro ⟨l,t,x,hx⟩ ⟨l',t',x',hx'⟩ h
    cases Prod.mk.inj h with
    | intro hl hrest =>
      cases hl
      obtain ⟨ht,hx⟩ := Prod.mk.inj hrest
      cases ht; cases hx; rfl)
instance [Fintype Q] [Fintype R] : Fintype (ExceptionalStep Q R) :=
  Fintype.ofInjective (fun g => (g.label,g.scalar)) (by
    rintro ⟨l,t,ht⟩ ⟨l',t',ht'⟩ h
    obtain ⟨hl,he⟩ := Prod.mk.inj h
    cases hl; cases he; rfl)

namespace PolygonStep
lemma eq_of_label_vector_eq (F : DirectionFrame Q A R E) {s t : PolygonStep Q R E}
    (hl : s.label = t.label) (hv : s.vector F = t.vector F) : s = t := by
  cases s with
  | inl g => cases t with
    | inl h =>
      have hgh := Sum.inl.inj hl
      cases g with
      | mk j c x hx => cases h with
        | mk j' c' x' hx' =>
          dsimp at hgh
          cases hgh
          have hh := F.u_injective j hv
          obtain ⟨hc,he⟩ := Prod.mk.inj hh
          cases hc; cases he; rfl
    | inr h => cases hl
  | inr g => cases t with
    | inl h => cases hl
    | inr h =>
      have hgh := Sum.inr.inj hl
      cases g with
      | mk r c hc => cases h with
        | mk r' c' hc' =>
          dsimp at hgh
          cases hgh
          have hh := F.exc_injective r hv
          cases hh; rfl

lemma vector_mem_label (F : DirectionFrame Q A R E) (s : PolygonStep Q R E) :
    s.vector F ∈ Sum.elim F.U F.exceptional s.label := by
  cases s with
  | inl g => exact ⟨(g.scalar,g.component),rfl⟩
  | inr e => exact ⟨e.scalar,rfl⟩
end PolygonStep

structure Candidate (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ) where
  step : Fin k → PolygonStep Q R E
  point : Fin k → A
  shift : ∀ i, point (finRotate k i) - point i = (step i).vector F
  adjacent : ∀ i, (step i).label ≠ (step (finRotate k i)).label
  exceptional : ∀ i (e : ExceptionalStep Q R), step i = .inr e →
    point i ∈ T e.label ∧ point (finRotate k i) ∈ T e.label
  generic : ∃ i j, (step i).label = .inl j

namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) {k : ℕ}

@[ext] lemma ext {c d : Candidate F T k} (hs : c.step = d.step) (hp : c.point = d.point) : c=d := by
  cases c; cases d; cases hs; cases hp; rfl

instance [Fintype Q] [Fintype R] [Fintype E] [Fintype A] : Fintype (Candidate F T k) :=
  Fintype.ofInjective (fun c => (c.step,c.point)) (by
    intro c d h
    exact ext F T (congrArg Prod.fst h) (congrArg Prod.snd h))

lemma closed (c : Candidate F T k) : ∑ i, (c.step i).vector F = 0 :=
  F.closed_of_points c.step c.point c.shift

def labels (c : Candidate F T k) : Finset (R × Q) := genericLabels (fun i => (c.step i).label)

def positions (c : Candidate F T k) : Finset (Fin k) := genericPositions (fun i => (c.step i).label)

lemma count_eq_two (c : Candidate F T k) (hk : k ≤ 5) (j : R × Q) (hj : j ∈ c.labels) :
    (Finset.univ.filter (fun i => (c.step i).label = .inl j)).card = 2 :=
  F.generic_occurs_twice c.step hk (c.closed F T) c.adjacent j ((mem_genericLabels _ _).mp hj)

lemma labels_card_bounds (c : Candidate F T k) (hk : k ≤ 5) : 1 ≤ c.labels.card ∧ c.labels.card ≤ 2 := by
  refine ⟨?_,genericLabels_card_le_two _ hk (fun j hj => c.count_eq_two F T hk j hj)⟩
  rw [Finset.one_le_card]
  obtain ⟨i,j,hi⟩ := c.generic
  exact ⟨j,(mem_genericLabels _ _).mpr ⟨i,hi⟩⟩

lemma positions_card (c : Candidate F T k) (hk : k ≤ 5) : c.positions.card = 2*c.labels.card :=
  genericPositions_card_eq_twice _ (fun j hj => c.count_eq_two F T hk j hj)

/-- Coordinate recovery on a cyclic sequence, used for the rooted event counts. -/
lemma points_eq (c d : Candidate F T k) (hs : c.step = d.step) (i : Fin k)
    (hi : c.point i = d.point i) : c.point = d.point := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hd (j : Fin (n+1)) : c.point (finRotate _ j) - d.point (finRotate _ j) =
        c.point j-d.point j := by
      have hc := c.shift j
      have he := d.shift j
      rw [hs] at hc
      exact sub_eq_sub_iff_sub_eq_sub.mp (hc.trans he.symm)
    have hc : ∀ j : Fin (n+1), c.point j-d.point j = c.point 0-d.point 0 := by
      intro j
      induction j using Fin.induction with
      | zero => rfl
      | succ j hj =>
        have hh := hd j.castSucc
        have hr : finRotate (n+1) j.castSucc = j.succ := finRotate_of_lt j.isLt
        rw [hr] at hh
        exact hh.trans hj
    have hz : c.point 0-d.point 0 = 0 := (hc i).symm.trans (sub_eq_zero.mpr hi)
    funext j
    exact sub_eq_zero.mp ((hc j).trans hz)

end Candidate

/-- In a closed vector sequence, deleting two positions in disjoint direction
spaces leaves at most one completion. This supplies all polygon count
uniqueness, including the unpaired sides of a pentagon. -/
lemma two_position_recovery {I : Type u_5} [Fintype I] [DecidableEq I]
    (U W : Submodule Q A) (hUW : Disjoint U W) (a b : I) (hab : a ≠ b)
    (v v' : I → A) (ha : v a ∈ U) (ha' : v' a ∈ U)
    (hb : v b ∈ W) (hb' : v' b ∈ W)
    (hz : ∑ i, v i = 0) (hz' : ∑ i, v' i = 0)
    (he : ∀ i, i ≠ a → i ≠ b → v i = v' i) : v = v' := by
  have hsum : ∑ i, (v i-v' i) = 0 := by rw [Finset.sum_sub_distrib,hz,hz',sub_self]
  have hpair : (v a-v' a)+(v b-v' b) = 0 := by
    have hs : ∑ i : I, (v i-v' i) = ∑ i ∈ ({a,b} : Finset I), (v i-v' i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
      exact sub_eq_zero.mpr (he i hi.1 hi.2)
    rw [hs] at hsum
    simpa only [Finset.sum_insert,Finset.mem_singleton,hab,not_false_eq_true,Finset.sum_singleton] using hsum
  have hwa : v a-v' a ∈ W := by
    have hneg : v a-v' a = -(v b-v' b) := eq_neg_of_add_eq_zero_left hpair
    rw [hneg]
    exact W.neg_mem (W.sub_mem hb hb')
  have hza := (Submodule.disjoint_def.mp hUW) _ (U.sub_mem ha ha') hwa
  have hzb : v b-v' b = 0 := by simpa only [hza,zero_add] using hpair
  funext i
  by_cases hi : i=a
  · subst i; exact sub_eq_zero.mp hza
  by_cases hi' : i=b
  · subst i; exact sub_eq_zero.mp hzb
  exact he i hi hi'

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
