import OAI.RingTheory.DirectFiniteness.DirectionSpaces

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {ι : Type u_3} [Field Q] [AddCommGroup A] [Module Q A]

lemma ShortDirect.finset_sum {m : ℕ} {P : ι → Submodule Q A}
    (h : ShortDirect m P) (s : Finset ι) (hs : s.card ≤ m)
    (x : ι → A) (hx : ∀ i ∈ s, x i ∈ P i) (hz : ∑ i ∈ s, x i = 0) :
    ∀ i ∈ s, x i = 0 := by
  let e : Fin s.card ≃ s := (s.equivFin).symm
  have hh := h s.card hs (fun i => (e i).val)
    (fun i j hij => e.injective (Subtype.ext hij)) (fun i => x (e i).val)
    (fun i => hx _ (e i).property)
  have hh' : ∑ i : Fin s.card, x (e i).val = 0 := by
    rw [← hz]
    exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).trans (Finset.sum_coe_sort s x)
  intro i hi
  simpa using hh hh' (e.symm ⟨i,hi⟩)

lemma ShortDirect.grouped_sum {m : ℕ} {P : ι → Submodule Q A}
    (h : ShortDirect m P) {τ : Type u_4} (s : Finset τ) (hs : s.card ≤ m)
    (label : τ → ι) (x : τ → A) (hx : ∀ t ∈ s, x t ∈ P (label t))
    (hz : ∑ t ∈ s, x t = 0) :
    ∀ i, ∑ t ∈ s.filter (fun t => label t = i), x t = 0 := by
  let supp := s.image label
  let y : ι → A := fun i => ∑ t ∈ s.filter (fun t => label t = i), x t
  have hy (i : ι) : y i ∈ P i := by
    apply Submodule.sum_mem
    intro t ht
    obtain ⟨hts,he⟩ := Finset.mem_filter.mp ht
    rw [← he]
    exact hx t hts
  have hyz : ∑ i ∈ supp, y i = 0 := by
    rw [← hz]
    exact Finset.sum_fiberwise_of_maps_to (fun t ht => Finset.mem_image_of_mem label ht) x
  intro i
  by_cases hi : i ∈ supp
  · exact h.finset_sum supp ((Finset.card_image_le).trans hs) y (fun i _ => hy i) hyz i hi
  · have he : s.filter (fun t => label t = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
      exact hi (he ▸ Finset.mem_image_of_mem label ht)
    rw [he, Finset.sum_empty]

lemma ShortDirect.disjoint {m : ℕ} {P : ι → Submodule Q A}
    (h : ShortDirect m P) (hm : 2 ≤ m) {i j : ι} (hij : i ≠ j) :
    Disjoint (P i) (P j) := by
  rw [Submodule.disjoint_def]
  intro x hxi hxj
  have he : ∑ t ∈ ({i,j} : Finset ι), (if t = i then x else -x) = 0 := by
    simp [hij, hij.symm]
  have hz := h.finset_sum {i,j} (by simpa [hij] using hm)
    (fun t => if t = i then x else -x) (by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with ht | ht
      · subst t; simpa using hxi
      · subst t; simpa [hij.symm] using (P j).neg_mem hxj) he i (by simp)
  simpa using hz

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
