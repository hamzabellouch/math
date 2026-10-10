import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Two Strip. -/

section

noncomputable section

namespace Saxl.Balance

def FourInterlacing (a b c d x y z w : ℕ) : Prop :=
  x ≤ a ∧ b ≤ x ∧ y ≤ b ∧ c ≤ y ∧ z ≤ c ∧ d ≤ z ∧ w ≤ d ∧
  x+y+z+w+2 = a+b+c+d ∧ (y < x ∨ w < z)

lemma four_interlacing_exists (a b c d : ℕ) (hab : b ≤ a) (hbc : c ≤ b)
    (hcd : d ≤ c) (ha : 3 ≤ a) :
    ∃ x y z w, FourInterlacing a b c d x y z w := by
  by_cases hd2 : 2 ≤ d
  · exact ⟨a,b,c,d-2,by unfold FourInterlacing; omega⟩
  by_cases hd1 : d = 1
  · by_cases hab' : b < a
    · exact ⟨a-1,b,c,d-1,by unfold FourInterlacing; omega⟩
    · by_cases hbc' : c < b
      · exact ⟨a,b-1,c,d-1,by unfold FourInterlacing; omega⟩
      · exact ⟨a,b,c-1,d-1,by unfold FourInterlacing; omega⟩
  have hd0 : d = 0 := by omega
  by_cases hc3 : 3 ≤ c
  · exact ⟨a,b,c-2,d,by unfold FourInterlacing; omega⟩
  by_cases hc2 : c = 2
  · by_cases hab' : b < a
    · exact ⟨a,b,c-2,d,by unfold FourInterlacing; omega⟩
    · exact ⟨a,b-1,c-1,d,by unfold FourInterlacing; omega⟩
  by_cases hc1 : c = 1
  · by_cases hb2 : 2 ≤ b
    · exact ⟨a,b-1,c-1,d,by unfold FourInterlacing; omega⟩
    · exact ⟨a-1,b,c-1,d,by unfold FourInterlacing; omega⟩
  by_cases hb2 : 2 ≤ b
  · exact ⟨a,b-2,c,d,by unfold FourInterlacing; omega⟩
  by_cases hb1 : b = 1
  · exact ⟨a-1,b-1,c,d,by unfold FourInterlacing; omega⟩
  · exact ⟨a-2,b,c,d,by unfold FourInterlacing; omega⟩

lemma horizontal_of_interlacing (ν μ : YoungDiagram)
    (hsub : ∀ i, ν.rowLen i ≤ μ.rowLen i)
    (hbtw : ∀ i, μ.rowLen (i+1) ≤ ν.rowLen i) : HorizontalStrip ν μ := by
  constructor
  · intro x hx
    exact YoungDiagram.mem_iff_lt_rowLen.mpr
      ((YoungDiagram.mem_iff_lt_rowLen.mp hx).trans_le (hsub x.1))
  · intro x hx hxν y hy hyν hxy
    apply Prod.ext _ hxy
    have hh : ∀ (p q : ℕ × ℕ), p ∈ μ → p ∉ ν → q ∈ μ → q ∉ ν →
        p.2 = q.2 → ¬ p.1 < q.1 := by
      intro p q _ hp hq _ hpq hlt
      have hp' := mt YoungDiagram.mem_iff_lt_rowLen.mpr hp
      have hq' := YoungDiagram.mem_iff_lt_rowLen.mp hq
      have hb := (μ.rowLen_anti _ _ (show p.1+1 ≤ q.1 by omega)).trans (hbtw p.1)
      omega
    exact Nat.le_antisymm (Nat.le_of_not_gt (hh y x hy hyν hx hxν hxy.symm))
      (Nat.le_of_not_gt (hh x y hx hxν hy hyν hxy))

lemma sorted_four (x y z w : ℕ) (hxy : y ≤ x) (hyz : z ≤ y) (hzw : w ≤ z) :
    [x,y,z,w].SortedGE := by
  simp [List.sortedGE_iff_pairwise, List.pairwise_cons]
  omega

lemma ofRowLens_height (A : List ℕ) (hA : A.SortedGE) :
    (YoungDiagram.ofRowLens A hA).colLen 0 ≤ A.length := by
  by_contra hh
  have h := YoungDiagram.mem_iff_lt_colLen.mpr
    (show A.length < (YoungDiagram.ofRowLens A hA).colLen 0 by omega)
  obtain ⟨h',_⟩ := YoungDiagram.mem_ofRowLens.mp h
  exact (Nat.lt_irrefl _) h'

lemma ofRowLens_rowLen (A : List ℕ) (hA : A.SortedGE) (i : ℕ) :
    (YoungDiagram.ofRowLens A hA).rowLen i = A[i]?.getD 0 := by
  by_cases hi : i < A.length
  · simpa [hi] using YoungDiagram.rowLen_ofRowLens (hw := hA) ⟨i,hi⟩
  · rw [rowLen_zero_of_height_le _ ((ofRowLens_height A hA).trans (by omega))]
    simp [List.getElem?_eq_none (by omega : A.length ≤ i)]

lemma card_of_height_four (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 4) :
    μ.card = μ.rowLen 0 + μ.rowLen 1 + μ.rowLen 2 + μ.rowLen 3 := by
  rw [← rowPrefix_eq_card μ hμ]
  simp [rowPrefix, Finset.sum_range_succ, add_assoc]

lemma odd_column_of_row_gap (μ : YoungDiagram) (i : ℕ) (hi : Even i)
    (hgap : μ.rowLen (i+1) < μ.rowLen i) : ∃ j, Odd (μ.colLen j) := by
  let j := μ.rowLen (i+1)
  have h₁ : i < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp
    (YoungDiagram.mem_iff_lt_rowLen.mpr hgap)
  have h₂ : ¬ i+1 < μ.colLen j := by
    intro h
    have hh := YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr h)
    exact Nat.lt_irrefl j hh
  refine ⟨j, ?_⟩
  have hlen : μ.colLen j = i+1 := by omega
  rw [hlen, Nat.odd_iff]
  have := Nat.even_iff.mp hi
  omega

theorem horizontal_two_odd_precursor (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ 4)
    (hw : 3 ≤ μ.rowLen 0) :
    ∃ ν : YoungDiagram, ν.card+2 = μ.card ∧ ν.colLen 0 ≤ 4 ∧
      (∃ j, Odd (ν.colLen j)) ∧ HorizontalStrip ν μ := by
  obtain ⟨x,y,z,w,hh⟩ := four_interlacing_exists
    (μ.rowLen 0) (μ.rowLen 1) (μ.rowLen 2) (μ.rowLen 3)
    (μ.rowLen_anti _ _ (by omega)) (μ.rowLen_anti _ _ (by omega))
    (μ.rowLen_anti _ _ (by omega)) hw
  have hs := sorted_four x y z w (hh.2.2.1.trans hh.2.1)
    (hh.2.2.2.2.1.trans hh.2.2.2.1) (hh.2.2.2.2.2.2.1.trans hh.2.2.2.2.2.1)
  let ν := YoungDiagram.ofRowLens [x,y,z,w] hs
  have hheight : ν.colLen 0 ≤ 4 := ofRowLens_height [x,y,z,w] hs
  have hrows (i : ℕ) : ν.rowLen i = [x,y,z,w][i]?.getD 0 := ofRowLens_rowLen _ _ _
  have h0 : ν.rowLen 0 = x := by simp [hrows]
  have h1 : ν.rowLen 1 = y := by simp [hrows]
  have h2 : ν.rowLen 2 = z := by simp [hrows]
  have h3 : ν.rowLen 3 = w := by simp [hrows]
  refine ⟨ν, ?_, hheight, ?_, ?_⟩
  · rw [card_of_height_four _ hheight, card_of_height_four μ hμ, h0, h1, h2, h3]
    exact hh.2.2.2.2.2.2.2.1
  · rcases hh.2.2.2.2.2.2.2.2 with h | h
    · exact odd_column_of_row_gap ν 0 (by decide) (by simpa only [h0,h1] using h)
    · exact odd_column_of_row_gap ν 2 (by decide) (by simpa only [h2,h3] using h)
  · apply horizontal_of_interlacing
    · intro i
      by_cases hi : i < 4
      · interval_cases i <;> simp only [h0,h1,h2,h3] <;> unfold FourInterlacing at hh <;> omega
      · rw [rowLen_zero_of_height_le _ (hheight.trans (by omega))]
        exact Nat.zero_le _
    · intro i
      by_cases hi : i < 3
      · interval_cases i <;> simp only [Nat.reduceAdd, h0,h1,h2] <;> unfold FourInterlacing at hh <;> omega
      · rw [rowLen_zero_of_height_le _ (hμ.trans (by omega))]
        exact Nat.zero_le _

theorem two_path_strip_restriction (q : ℕ) (hq : 3 ≤ q)
    (μ : YoungDiagram) (hsize : μ.card = 2*q+4) (hμ : μ.colLen 0 ≤ 4)
    (t : Tableau (2*q+4) μ) :
    ∃ (ν : YoungDiagram) (hν : ν.card = 2*q+2) (hs : HorizontalStrip ν μ),
      ν.colLen 0 ≤ 4 ∧ (∃ j, Odd (ν.colLen j)) ∧
      ∃ F : Specht t →ₗ[ℂ] Specht (canonicalTableau ν hν), Function.Surjective F ∧
        ∀ (g : Equiv.Perm (Fin (2*q+4))) (h : Equiv.Perm (Fin (2*q+2))),
          (∀ k, g (tableauInclusion (canonicalTableau ν hν) t hs.1 k) =
            tableauInclusion (canonicalTableau ν hν) t hs.1 (h k)) →
          ∀ v, F (spechtRep t g v) = spechtRep (canonicalTableau ν hν) h (F v) := by
  have hw : 3 ≤ μ.rowLen 0 := by
    have hc := card_of_height_four μ hμ
    have h1 := μ.rowLen_anti 0 1 (by omega)
    have h2 := μ.rowLen_anti 0 2 (by omega)
    have h3 := μ.rowLen_anti 0 3 (by omega)
    omega
  obtain ⟨ν,hcard,hheight,hodd,hs⟩ := horizontal_two_odd_precursor μ hμ hw
  have hν : ν.card = 2*q+2 := by omega
  obtain ⟨F,hF,hFeq⟩ := pieri_strip_surjective (canonicalTableau ν hν) t hs
  exact ⟨ν,hν,hs,hheight,hodd,F,hF,hFeq⟩

end Saxl.Balance
end
end

end OAI
