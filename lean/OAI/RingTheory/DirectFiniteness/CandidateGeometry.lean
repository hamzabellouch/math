import OAI.RingTheory.DirectFiniteness.LabelSupport

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E]

lemma cyclic_two_apart (k : ℕ) (hk3 : 3 ≤ k) (hk5 : k ≤ 5) :
    ∀ i j : Fin k, i ≠ j → finRotate k i ≠ j → finRotate k j ≠ i →
      finRotate k (finRotate k i) = j ∨ finRotate k (finRotate k j) = i := by
  interval_cases k <;> decide

namespace DirectionFrame
variable (F : DirectionFrame Q A R E)

lemma vector_mem_U {s : PolygonStep Q R E} {j : R × Q} (hs : s.label = .inl j) :
    s.vector F ∈ F.U j := by
  cases s with
  | inl g => cases Sum.inl.inj hs; exact ⟨(g.scalar,g.component),rfl⟩
  | inr e => cases hs

lemma vector_not_mem_U {s : PolygonStep Q R E} {j : R × Q} (hs : s.label ≠ .inl j) :
    s.vector F ∉ F.U j := by
  intro hm
  cases s with
  | inl g =>
    have hgj : g.label ≠ j := fun he => hs (congrArg Sum.inl he)
    have hz := (Submodule.disjoint_def.mp (F.U_disjoint hgj))
      ((PolygonStep.vector F (.inl g))) ⟨(g.scalar,g.component),rfl⟩ hm
    exact PolygonStep.vector_ne_zero F (.inl g) hz
  | inr e =>
    have hz := (Submodule.disjoint_def.mp (F.U_exceptional_disjoint j e.label))
      ((PolygonStep.vector F (.inr e))) hm ⟨e.scalar,rfl⟩
    exact PolygonStep.vector_ne_zero F (.inr e) hz

lemma two_generic_bundle {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (hk : k ≤ 5) (hz : ∑ i, (s i).vector F = 0)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label)
    (hg : (genericLabels (fun i => (s i).label)).card = 2)
    (r : R) (hr : ∃ i, (s i).label = .inr r) :
    k = 5 ∧ ∀ j ∈ genericLabels (fun i => (s i).label), j.1 = r := by
  have hc : ∀ j ∈ genericLabels (fun i => (s i).label),
      (Finset.univ.filter (fun i => (s i).label = .inl j)).card = 2 := by
    intro j hj
    exact F.generic_occurs_twice s hk hz hadj j ((mem_genericLabels _ _).mp hj)
  obtain ⟨hk5,hcr⟩ := exceptional_count_singleton_of_two_generic _ hk hc hg r hr
  obtain ⟨i,i',g,g',hi,hi',hr',hr'',hne⟩ :=
    F.singleton_exceptional_two_slopes s hk hz r hcr
  have hne' : g.label ≠ g'.label := fun h => hne (congrArg Prod.snd h)
  have hsub : {g.label,g'.label} ⊆ genericLabels (fun i => (s i).label) := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact (mem_genericLabels _ _).mpr ⟨i,by simp [hi,PolygonStep.label]⟩
    · exact (mem_genericLabels _ _).mpr ⟨i',by simp [hi',PolygonStep.label]⟩
  have he : genericLabels (fun i => (s i).label) = {g.label,g'.label} := by
    exact (Finset.eq_of_subset_of_card_le hsub (by simp [hg,hne'])).symm
  refine ⟨hk5,?_⟩
  intro j hj
  rw [he] at hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact hr'
  · exact hr''

lemma distinct_generic_cosets [Fintype A] {k : ℕ} (s : Fin k → PolygonStep Q R E)
    (pt : Fin k → A) (hk3 : 3 ≤ k) (hk5 : k ≤ 5)
    (hpt : ∀ i, pt (finRotate k i) - pt i = (s i).vector F)
    (hadj : ∀ i, (s i).label ≠ (s (finRotate k i)).label)
    {i i' : Fin k} (hii : i ≠ i') {j : R × Q}
    (hi : (s i).label = .inl j) (hi' : (s i').label = .inl j) :
    AffineCoset.of (F.U j) (pt i) ≠ AffineCoset.of (F.U j) (pt i') := by
  have hr : finRotate k i ≠ i' := fun h => hadj i (hi.trans (h ▸ hi').symm)
  have hr' : finRotate k i' ≠ i := fun h => hadj i' (hi'.trans (h ▸ hi).symm)
  have hh (a b : Fin k) (ha : (s a).label = .inl j)
      (hab : finRotate k (finRotate k a) = b)
      (hc : AffineCoset.of (F.U j) (pt a) = AffineCoset.of (F.U j) (pt b)) : False := by
    have hd : pt b - pt a ∈ F.U j := (AffineCoset.of_eq_iff _ _ _).mp hc.symm
    have hm : (s (finRotate k a)).vector F ∈ F.U j := by
      have hsub := (F.U j).sub_mem hd (F.vector_mem_U ha)
      rw [← hpt a] at hsub
      rw [← hpt (finRotate k a),hab]
      convert hsub using 1; abel
    exact F.vector_not_mem_U (fun he => hadj a (ha.trans he.symm)) hm
  intro hc
  rcases cyclic_two_apart k hk3 hk5 i i' hii hr hr' with h | h
  · exact hh i i' hi h hc
  · exact hh i' i hi' h hc.symm

lemma closed_of_points {k : ℕ} (s : Fin k → PolygonStep Q R E) (pt : Fin k → A)
    (hpt : ∀ i, pt (finRotate k i) - pt i = (s i).vector F) :
    ∑ i, (s i).vector F = 0 := by
  simp_rw [← hpt]
  rw [Finset.sum_sub_distrib,Equiv.sum_comp (finRotate k),sub_self]

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
