import OAI.RingTheory.DirectFiniteness.HoleExistence

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry

/-- In a cyclic sequence of at most five positions with unequal neighboring
labels, no label can occur thrice. This includes the wrap-around adjacency. -/
lemma cyclic_label_count_le_two {k : ℕ} {L : Type u_1} [DecidableEq L] (lab : Fin k → L)
    (hk : k ≤ 5) (hadj : ∀ i, lab i ≠ lab (finRotate k i)) (l : L) :
    ((Finset.univ : Finset (Fin k)).filter (fun i => lab i = l)).card ≤ 2 := by
  let s := (Finset.univ : Finset (Fin k)).filter (fun i => lab i = l)
  have hd : Disjoint s (s.image (finRotate k)) := by
    rw [Finset.disjoint_left]
    intro i hi hir
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hir
    exact hadj j ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hi).2.symm)
  have hc : s.card + (s.image (finRotate k)).card ≤ k := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Fintype.card_fin k)
  rw [Finset.card_image_of_injective _ (finRotate k).injective] at hc
  dsimp [s] at hc
  omega

/-- A nonzero vector cannot be the sole contribution to a zero sum. -/
lemma count_ne_one_of_sum_eq_zero {I : Type u_2} {L : Type u_3} {M : Type u_4} [Fintype I] [DecidableEq L]
    [AddCommGroup M] (lab : I → L) (v : I → M) (l : L)
    (hn : ∀ i, lab i = l → v i ≠ 0)
    (hz : ∑ i ∈ (Finset.univ : Finset I).filter (fun i => lab i = l), v i = 0) :
    ((Finset.univ : Finset I).filter (fun i => lab i = l)).card ≠ 1 := by
  intro hc
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hc
  have hi' : i ∈ (Finset.univ : Finset I).filter (fun i => lab i = l) := by rw [hi]; simp
  have hil : lab i = l := (Finset.mem_filter.mp hi').2
  rw [hi,Finset.sum_singleton] at hz
  exact hn i hil hz

lemma cyclic_label_count_eq_two {k : ℕ} {L : Type u_5} {M : Type u_6} [DecidableEq L] [AddCommGroup M]
    (lab : Fin k → L) (v : Fin k → M) (hk : k ≤ 5)
    (hadj : ∀ i, lab i ≠ lab (finRotate k i)) (l : L)
    (hne : ∃ i, lab i = l) (hn : ∀ i, lab i = l → v i ≠ 0)
    (hz : ∑ i ∈ (Finset.univ : Finset (Fin k)).filter (fun i => lab i = l), v i = 0) :
    ((Finset.univ : Finset (Fin k)).filter (fun i => lab i = l)).card = 2 := by
  have hle := cyclic_label_count_le_two lab hk hadj l
  have hne1 := count_ne_one_of_sum_eq_zero lab v l hn hz
  have hp : 0 < ((Finset.univ : Finset (Fin k)).filter (fun i => lab i = l)).card := by
    rw [Finset.card_pos]
    obtain ⟨i,hi⟩ := hne
    exact ⟨i,by simp [hi]⟩
  omega

/-- Occurrence-count form of the pigeonhole bound, retaining the exact support. -/
lemma sum_label_counts {I : Type u_7} {L : Type u_8} [Fintype I] [DecidableEq L] (lab : I → L) :
    ∑ l ∈ Finset.univ.image lab,
      ((Finset.univ : Finset I).filter (fun i => lab i = l)).card = Fintype.card I := by
  symm
  simpa using Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset I))
    (t := Finset.univ.image lab) (f := lab) (fun i hi => Finset.mem_image_of_mem lab hi)

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
