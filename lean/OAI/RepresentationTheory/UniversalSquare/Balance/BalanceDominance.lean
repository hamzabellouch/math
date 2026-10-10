import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.Capacity

namespace OAI

/-! Balance Dominance. -/

section

noncomputable section

namespace UniversalTensorSquare
open Saxl

lemma rowPrefix_scaled_mono (μ : YoungDiagram) {k l : ℕ} (hkl : k ≤ l) :
    k * rowPrefix μ l ≤ l * rowPrefix μ k := by
  induction l, hkl using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih =>
    have hlast : k * μ.rowLen l ≤ rowPrefix μ k := by
      have h := Finset.sum_le_sum (s := Finset.range k) (f := fun _ => μ.rowLen l)
        (g := μ.rowLen) (by
          intro i hi
          exact μ.rowLen_anti _ _ (by have := Finset.mem_range.mp hi; omega))
      simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, rowPrefix] using h
    rw [rowPrefix_succ]
    nlinarith

lemma colPrefix_eq_min_sum (μ : YoungDiagram) (k : ℕ) :
    colPrefix μ k = ∑ i ∈ Finset.range (μ.colLen 0), min k (μ.rowLen i) := by
  rw [← colTruncate_card, ← rowPrefix_eq_card _ (colTruncate_height μ k)]
  exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)

lemma scaled_colPrefix_lower (A : YoungDiagram) {k B : ℕ}
    (hB : A.rowLen 0 ≤ B) (hk : k ≤ B) :
    k*A.card ≤ B*colPrefix A k := by
  rw [colPrefix_eq_min_sum, ← rowPrefix_eq_card A le_rfl]
  simp only [rowPrefix, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : A.rowLen i ≤ B := (A.rowLen_anti _ _ (Nat.zero_le _)).trans hB
  by_cases hh : k ≤ A.rowLen i
  · rw [min_eq_left hh]
    nlinarith
  · rw [min_eq_right (by omega)]
    exact Nat.mul_le_mul_right _ hk

theorem balance_dominance (M : ℕ) (hM : 9 ≤ M) (μ A : YoungDiagram)
    (hc : μ.card = A.card) (hn : (staircase M).card ≤ μ.card)
    (hμ : colPrefix μ 4 ≤ 2*M-2)
    (hparts : 2*M-5 ≤ A.colLen 0) (hmax : A.rowLen 0 ≤ M+1)
    (hfour : 2 ≤ A.rowLen 3) : Dominates μ A := by
  have hdouble := staircase_card_double M
  have hn' : M*(M+1) ≤ 2*μ.card := by omega
  have hlarge : 2*M-2 < μ.card := by
    have hs : M*M ≥ 9*M := Nat.mul_le_mul_right M hM
    have hsub : 2*M-2 ≤ 2*M := Nat.sub_le _ _
    nlinarith
  have hwidth : 4 ≤ μ.rowLen 0 := by
    by_contra hh
    have he : colPrefix μ 4 = μ.card := by
      simpa only [colPrefix, YoungDiagram.colLen_transpose, transpose_card] using
        rowPrefix_eq_card μ.transpose (by simpa using (show μ.rowLen 0 ≤ 4 by omega))
    omega
  have hpos (i : ℕ) (hi : i < 4) : 1 ≤ μ.colLen i := by
    have hh := YoungDiagram.mem_iff_lt_colLen.mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr (show i < μ.rowLen 0 by omega))
    omega
  have hheight : μ.colLen 0 ≤ 2*M-5 := by
    have hp1 := hpos 1 (by decide)
    have hp2 := hpos 2 (by decide)
    have hp3 := hpos 3 (by decide)
    rw [colPrefix_eq_sum] at hμ
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hμ
    omega
  have hA1 : 4 ≤ A.colLen 1 := by
    have h := YoungDiagram.mem_iff_lt_colLen.mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr (show 1 < A.rowLen 3 by omega))
    omega
  have hA2 : 2*M-1 ≤ colPrefix A 2 := by
    rw [colPrefix_eq_sum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    omega
  have hdual : Dominates A.transpose μ.transpose := by
    intro k
    change colPrefix μ k ≤ colPrefix A k
    by_cases hk : k < 4
    · interval_cases k
      · simp [colPrefix, rowPrefix]
      · simpa only [colPrefix_eq_sum, Finset.sum_range_one] using hheight.trans hparts
      · exact ((rowPrefix_mono μ.transpose (by omega)).trans hμ).trans (by omega)
      · have hA3 := rowPrefix_mono A.transpose (show 2 ≤ 3 by omega)
        change colPrefix A 2 ≤ colPrefix A 3 at hA3
        exact ((rowPrefix_mono μ.transpose (by omega)).trans hμ).trans (by omega)
    · by_cases hB : A.rowLen 0 ≤ k
      · have he : colPrefix A k = A.card := by
          simpa only [colPrefix, transpose_card] using
            rowPrefix_eq_card A.transpose (by simpa using hB)
        rw [he, ← hc]
        exact (rowPrefix_le_card μ.transpose k).trans_eq (transpose_card _)
      · let B := A.rowLen 0
        have hBp : 0 < B := by dsimp only [B]; omega
        have hupper : 4*colPrefix μ k ≤ k*(2*M-2) :=
          (rowPrefix_scaled_mono μ.transpose (by omega)).trans
            (Nat.mul_le_mul_left k hμ)
        have hlower := scaled_colPrefix_lower A le_rfl (show k ≤ B by dsimp [B]; omega)
        have hratio : B*(2*M-2) ≤ 4*A.card := by
          have hmul := Nat.mul_le_mul_right (2*M-2) hmax
          dsimp only [B]
          have hsub : 2*M-2+2 = 2*M := by omega
          nlinarith
        have hbound : (4*B)*colPrefix μ k ≤ (4*B)*colPrefix A k := calc
          (4*B)*colPrefix μ k = B*(4*colPrefix μ k) := by ring
          _ ≤ B*(k*(2*M-2)) := Nat.mul_le_mul_left B hupper
          _ = k*(B*(2*M-2)) := by ring
          _ ≤ k*(4*A.card) := Nat.mul_le_mul_left k hratio
          _ = 4*(k*A.card) := by ring
          _ ≤ 4*(B*colPrefix A k) := Nat.mul_le_mul_left 4 hlower
          _ = (4*B)*colPrefix A k := by ring
        exact (mul_le_mul_iff_right₀ (show 0 < 4*B by omega)).mp hbound
  simpa only [YoungDiagram.transpose_transpose] using
    dominates_transpose (by simpa only [transpose_card] using hc.symm) hdual

theorem balance_invariant_functional (M : ℕ) (hM : 9 ≤ M) (μ A : YoungDiagram)
    (hc : μ.card = A.card) (hn : (staircase M).card ≤ μ.card)
    (hμ : colPrefix μ 4 ≤ 2*M-2)
    (hparts : 2*M-5 ≤ A.colLen 0) (hmax : A.rowLen 0 ≤ M+1)
    (hfour : 2 ≤ A.rowLen 3) :
    ∃ (a : Fin μ.card → Fin (A.colLen 0)) (l : Module.Dual ℂ (Specht (shapeTableau μ))),
      l ≠ 0 ∧
      (∀ j, (Finset.univ.filter (fun i => a i = j)).card = A.rowLen j) ∧
      (∀ g : Equiv.Perm (Fin μ.card), a ∘ g = a →
        ∀ x, l (spechtRep (shapeTableau μ) g x) = l x) := by
  exact young_invariant_functional A μ hc
    (balance_dominance M hM μ A hc hn hμ hparts hmax hfour)

end UniversalTensorSquare
end
end

end OAI
