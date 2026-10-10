import OAI.RingTheory.DirectFiniteness.CandidateRelations

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

def transverse (α : Q) : (Q × Q) →ₗ[Q] Q where
  toFun x := x.2 - x.1 * α
  map_add' x y := by dsimp; ring
  map_smul' c x := by dsimp; ring

lemma exceptional_scalar_sum {k : ℕ} (s : Fin k → PolygonStep Q R E) (hk : k ≤ 5)
    (hz : ∑ i, (s i).vector F = 0) (r : R) (α : Q)
    (hslope : ∀ i (g : GenericStep Q R E), s i = .inl g → g.label.1 = r → g.label.2 = α) :
    ∑ i ∈ Finset.univ.filter (fun i => (s i).label = .inr r),
      Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (s i) = 0 := by
  have h := congrArg (transverse α) ((F.polygon_component_sums s hk hz).2 r)
  rw [map_sum,map_zero,Finset.sum_filter] at h
  rw [Finset.sum_filter]
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  cases hi : s i with
  | inl g =>
    simp only [PolygonStep.label,reduceCtorEq,ite_false,
      PolygonStep.bundle,PolygonStep.wcoord]
    by_cases hr : g.label.1 = r
    · simp [hr,transverse,hslope i g hi hr]
    · simp [hr]
  | inr e =>
    simp only [PolygonStep.label,Sum.inr.injEq,PolygonStep.bundle,PolygonStep.wcoord]
    by_cases hr : e.label = r <;> simp [hr,transverse]

lemma exceptional_occurs_twice_single_slope {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (hk : k ≤ 5) (hz : ∑ i, (s i).vector F = 0)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label) (r : R)
    (hr : ∃ i, (s i).label = .inr r) (α : Q)
    (hslope : ∀ i (g : GenericStep Q R E), s i = .inl g → g.label.1 = r → g.label.2 = α) :
    (Finset.univ.filter (fun i => (s i).label = .inr r)).card = 2 := by
  apply cyclic_label_count_eq_two (fun i => (s i).label)
    (fun i => Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (s i))
    hk hadj (.inr r) hr
  · intro i hi
    cases h : s i with
    | inl g => simp [h,PolygonStep.label] at hi
    | inr e => exact e.nonzero
  · exact F.exceptional_scalar_sum s hk hz r α hslope

lemma all_labels_twice_length {k : ℕ} {L : Type u_5} [DecidableEq L] (lab : Fin k → L)
    (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (hcount : ∀ l ∈ Finset.univ.image lab,
      (Finset.univ.filter (fun i => lab i = l)).card = 2) :
    k = 4 ∧ (Finset.univ.image lab).card = 2 := by
  have h := sum_label_counts lab
  have he : (∑ l ∈ Finset.univ.image lab,
      (Finset.univ.filter (fun i => lab i = l)).card) =
      (Finset.univ.image lab).card * 2 := by
    calc
      _ = ∑ _l ∈ Finset.univ.image lab, 2 := Finset.sum_congr rfl hcount
      _ = _ := by simp
  rw [he,Fintype.card_fin] at h
  omega

/-- With at most one generic label every occurring label occurs twice, so the
candidate is a four-step rectangle. -/
lemma one_generic_rectangle {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (hz : ∑ i, (s i).vector F = 0)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label)
    (j : R × Q) (honly : ∀ i (g : GenericStep Q R E), s i = .inl g → g.label = j) :
    k = 4 ∧ (Finset.univ.image (fun i => (s i).label)).card = 2 := by
  apply all_labels_twice_length _ hk3 hk5
  intro l hl
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hl
  cases l with
  | inl j' => exact F.generic_occurs_twice s hk5 hz hadj j' ⟨i,hi⟩
  | inr r =>
    apply F.exceptional_occurs_twice_single_slope s hk5 hz hadj r ⟨i,hi⟩ j.2
    intro i g hg _
    exact congrArg Prod.snd (honly i g hg)

/-- A lone exceptional step requires two different generic slopes in its own
bundle. This is the cancellation needed for the pentagon count. -/
lemma singleton_exceptional_two_slopes {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (hk : k ≤ 5) (hz : ∑ i, (s i).vector F = 0) (r : R)
    (hc : (Finset.univ.filter (fun i => (s i).label = .inr r)).card = 1) :
    ∃ (i i' : Fin k) (g g' : GenericStep Q R E), s i = .inl g ∧ s i' = .inl g' ∧
      g.label.1 = r ∧ g'.label.1 = r ∧ g.label.2 ≠ g'.label.2 := by
  by_contra hh
  push Not at hh
  have hslope : ∃ α : Q, ∀ i (g : GenericStep Q R E),
      s i = .inl g → g.label.1 = r → g.label.2 = α := by
    by_cases hex : ∃ (i : Fin k) (g : GenericStep Q R E), s i = .inl g ∧ g.label.1 = r
    · obtain ⟨i,g,hi,hr⟩ := hex
      refine ⟨g.label.2,?_⟩
      intro i' g' hi' hr'
      exact (hh i i' g g' hi hi' hr hr').symm
    · refine ⟨0,?_⟩
      intro i g hi hr
      exact False.elim (hex ⟨i,g,hi,hr⟩)
  obtain ⟨α,hα⟩ := hslope
  have hn := count_ne_one_of_sum_eq_zero (fun i => (s i).label)
    (fun i => Sum.elim (fun _ => 0) (fun exceptional => exceptional.scalar) (s i)) (.inr r)
    (by
      intro i hi
      cases h : s i with
      | inl g => simp [h,PolygonStep.label] at hi
      | inr e => exact e.nonzero)
    (F.exceptional_scalar_sum s hk hz r α hα)
  exact hn hc

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
