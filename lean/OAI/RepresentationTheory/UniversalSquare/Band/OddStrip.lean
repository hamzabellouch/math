import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Odd Strip. -/

section

noncomputable section

namespace Saxl.Balance

lemma card_of_height_two (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 2) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 := by
  rw [← rowPrefix_eq_card μ hμ]
  simp [rowPrefix, Finset.sum_range_succ]

lemma short_rowLen (b δ i : ℕ) :
    (ShortColumns.shape b δ).rowLen i = if i = 0 then b+δ else if i = 1 then b else 0 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, ShortColumns.mem_shape]
  split_ifs <;> simp_all

lemma short_card (b δ : ℕ) :
    (ShortColumns.shape b δ).card = 2*b+δ := by
  rw [card_of_height_two _ (ShortColumns.height_le b δ)]
  simp [short_rowLen]
  omega

lemma horizontal_two_rows (ν μ : YoungDiagram)
    (hν : ν.colLen 0 ≤ 2) (hμ : μ.colLen 0 ≤ 2)
    (h0 : ν.rowLen 0 ≤ μ.rowLen 0) (h1 : ν.rowLen 1 ≤ μ.rowLen 1)
    (hm : μ.rowLen 1 ≤ ν.rowLen 0) : HorizontalStrip ν μ := by
  have row_lt (η : YoungDiagram) (hη : η.colLen 0 ≤ 2) (x : ℕ × ℕ)
      (hx : x ∈ η) : x.1 = 0 ∨ x.1 = 1 := by
    have hh := YoungDiagram.mem_iff_lt_colLen.mp
      (η.up_left_mem (le_refl x.1) (Nat.zero_le x.2) hx)
    omega
  constructor
  · intro x hx
    rw [YoungDiagram.mem_iff_lt_rowLen] at hx ⊢
    rcases row_lt ν hν x (YoungDiagram.mem_iff_lt_rowLen.mpr hx) with h | h
    · simpa only [h] using lt_of_lt_of_le (by simpa only [h] using hx) h0
    · simpa only [h] using lt_of_lt_of_le (by simpa only [h] using hx) h1
  · intro x hx hxn y hy hyn hxy
    apply Prod.ext _ hxy
    have hxr := row_lt μ hμ x hx
    have hyr := row_lt μ hμ y hy
    rw [YoungDiagram.mem_iff_lt_rowLen] at hx hy hxn hyn
    rcases hxr with hxr | hxr <;> rcases hyr with hyr | hyr
    · omega
    · simp only [hxr, hyr] at hx hy hxn hyn
      omega
    · simp only [hxr, hyr] at hx hy hxn hyn
      omega
    · omega

theorem odd_strip_precursor (c x : ℕ) (hc : Even c) (hx : Odd x)
    (hxc : x ≤ c) (μ : YoungDiagram) (hsize : μ.card = c+x)
    (hμ : μ.colLen 0 ≤ 2) :
    ∃ ν : YoungDiagram, ν.card = c ∧ ν.colLen 0 ≤ 2 ∧
      (∀ i, Even (ν.rowLen i)) ∧ HorizontalStrip ν μ := by
  let β := μ.rowLen 1
  let U := min β (c-β)
  let y := 2*(U/2)
  have hm := μ.rowLen_anti 0 1 (by omega)
  have hcard := card_of_height_two μ hμ
  have hcp := Nat.even_iff.mp hc
  have hxp := Nat.odd_iff.mp hx
  have hβ : β ≤ c := by dsimp only [β]; omega
  have huβ : U ≤ β := min_le_left _ _
  have huc : U ≤ c-β := min_le_right _ _
  have hyu : y ≤ U := by dsimp only [y]; omega
  have hyc : 2*y ≤ c := by omega
  have hyβ : β ≤ y+x := by
    dsimp only [β, U, y] at *
    omega
  have hyp : y % 2 = 0 := by dsimp only [y]; omega
  refine ⟨ShortColumns.shape y (c-2*y), ?_, ShortColumns.height_le _ _, ?_, ?_⟩
  · rw [short_card]
    omega
  · intro i
    rw [short_rowLen, Nat.even_iff]
    split_ifs <;> omega
  · apply horizontal_two_rows _ _ (ShortColumns.height_le _ _) hμ
    · simp only [short_rowLen, ite_true]
      dsimp only [β] at *
      omega
    · simpa only [short_rowLen, Nat.one_ne_zero, ite_false, ite_true] using
        hyu.trans huβ
    · simp only [short_rowLen, ite_true]
      dsimp only [β] at *
      omega

theorem odd_strip_restriction (c x : ℕ) (hc : Even c) (hx : Odd x)
    (hxc : x ≤ c) (μ : YoungDiagram) (hsize : μ.card = c+x)
    (hμ : μ.colLen 0 ≤ 2) (t : Tableau (c+x) μ) :
    ∃ (ν : YoungDiagram) (hν : ν.card = c) (hs : HorizontalStrip ν μ),
      ν.colLen 0 ≤ 2 ∧ (∀ i, Even (ν.rowLen i)) ∧
      ∃ F : Specht t →ₗ[ℂ] Specht (canonicalTableau ν hν), Function.Surjective F ∧
        ∀ (g : Equiv.Perm (Fin (c+x))) (h : Equiv.Perm (Fin c)),
          (∀ k, g (tableauInclusion (canonicalTableau ν hν) t hs.1 k) =
            tableauInclusion (canonicalTableau ν hν) t hs.1 (h k)) →
          ∀ v, F (spechtRep t g v) = spechtRep (canonicalTableau ν hν) h (F v) := by
  obtain ⟨ν,hν,hheight,he,hs⟩ := odd_strip_precursor c x hc hx hxc μ hsize hμ
  obtain ⟨f,hf,heq⟩ := pieri_strip_surjective (canonicalTableau ν hν) t hs
  exact ⟨ν,hν,hs,hheight,he,f,hf,heq⟩

end Saxl.Balance
end
end

end OAI
