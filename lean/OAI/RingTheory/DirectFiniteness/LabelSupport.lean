import OAI.RingTheory.DirectFiniteness.CandidateClassification

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {I : Type u_1} {J : Type u_2} {R : Type u_3} [Fintype I] [DecidableEq J] [DecidableEq R]

def genericLabels (lab : I → J ⊕ R) : Finset J := (Finset.univ.image lab).toLeft

def genericPositions (lab : I → J ⊕ R) : Finset I := Finset.univ.filter (fun i => (lab i).isLeft)

def exceptionalPositions (lab : I → J ⊕ R) : Finset I := Finset.univ.filter (fun i => (lab i).isRight)

@[simp] lemma mem_genericLabels (lab : I → J ⊕ R) (j : J) :
    j ∈ genericLabels lab ↔ ∃ i, lab i = .inl j := by simp [genericLabels]

lemma count_genericPositions (lab : I → J ⊕ R) :
    (genericPositions lab).card =
      ∑ j ∈ genericLabels lab, (Finset.univ.filter (fun i => lab i = .inl j)).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := genericPositions lab) (t := (genericLabels lab).image Sum.inl) (f := lab)
    (by
      intro i hi
      have hh : (lab i).isLeft := (Finset.mem_filter.mp hi).2
      cases he : lab i with
      | inl j => exact Finset.mem_image.mpr ⟨j,(mem_genericLabels lab j).mpr ⟨i,he⟩,rfl⟩
      | inr r => simp [he] at hh)
  rw [Finset.sum_image (by intro x _ y _ hxy; exact Sum.inl.inj hxy)] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,genericPositions]
  exact ⟨fun h => h.2,fun h => ⟨by simp [h],h⟩⟩

omit [DecidableEq J] [DecidableEq R] in
lemma card_generic_add_exceptional (lab : I → J ⊕ R) :
    (genericPositions lab).card + (exceptionalPositions lab).card = Fintype.card I := by
  have he : genericPositions lab ∪ exceptionalPositions lab = Finset.univ := by
    ext i
    cases h : lab i <;> simp [genericPositions,exceptionalPositions,h]
  have hd : Disjoint (genericPositions lab) (exceptionalPositions lab) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    cases h : lab i <;> simp_all [genericPositions,exceptionalPositions]
  rw [← Finset.card_union_of_disjoint hd,he,Finset.card_univ]

lemma genericPositions_card_eq_twice (lab : I → J ⊕ R)
    (hc : ∀ j ∈ genericLabels lab,
      (Finset.univ.filter (fun i => lab i = .inl j)).card = 2) :
    (genericPositions lab).card = 2 * (genericLabels lab).card := by
  rw [count_genericPositions]
  calc
    _ = ∑ _j ∈ genericLabels lab, 2 := Finset.sum_congr rfl hc
    _ = _ := by simp [mul_comm]

lemma genericLabels_card_le_two {k : ℕ} (lab : Fin k → J ⊕ R)
    (hk : k ≤ 5) (hc : ∀ j ∈ genericLabels lab,
      (Finset.univ.filter (fun i => lab i = .inl j)).card = 2) :
    (genericLabels lab).card ≤ 2 := by
  have h := card_generic_add_exceptional lab
  rw [genericPositions_card_eq_twice lab hc,Fintype.card_fin] at h
  omega

lemma exceptional_count_singleton_of_two_generic {k : ℕ} (lab : Fin k → J ⊕ R)
    (hk : k ≤ 5) (hc : ∀ j ∈ genericLabels lab,
      (Finset.univ.filter (fun i => lab i = .inl j)).card = 2)
    (hg : (genericLabels lab).card = 2) (r : R) (hr : ∃ i, lab i = .inr r) :
    k = 5 ∧ (Finset.univ.filter (fun i => lab i = .inr r)).card = 1 := by
  have h := card_generic_add_exceptional lab
  rw [genericPositions_card_eq_twice lab hc,hg,Fintype.card_fin] at h
  have hs : Finset.univ.filter (fun i => lab i = .inr r) ⊆ exceptionalPositions lab := by
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    simp [exceptionalPositions,hi]
  have hb := Finset.card_le_card hs
  have hp : 0 < (Finset.univ.filter (fun i => lab i = .inr r)).card := by
    rw [Finset.card_pos]
    obtain ⟨i,hi⟩ := hr
    exact ⟨i,by simp [hi]⟩
  omega

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
