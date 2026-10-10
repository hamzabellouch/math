import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.Intermediate

namespace OAI

/-! Refined Capacity. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma prefix_last_after_first (μ : YoungDiagram) {j : ℕ} (hj : 0 < j) :
    μ.rowLen 0 + (j-1)*μ.rowLen (j-1) ≤ rowPrefix μ j := by
  have he : j = (j-1)+1 := by omega
  unfold rowPrefix
  conv_rhs => rw [he, Finset.sum_range_succ']
  have hh := Finset.sum_le_sum (s := Finset.range (j-1))
    (f := fun _ => μ.rowLen (j-1)) (g := fun a => μ.rowLen (a+1)) (by
      intro a ha
      exact μ.rowLen_anti _ _ (by have := Finset.mem_range.mp ha; omega))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hh
  omega

def endpointBound (i U H : ℕ) : ℕ :=
  if i = 1 then U else min (U/i) ((U-H)/(i-1))

lemma endpointBound_sound (μ : YoungDiagram) {i U H : ℕ} (hi : 0 < i)
    (hU : rowPrefix μ i ≤ U) (hH : H ≤ μ.rowLen 0) :
    μ.rowLen (i-1) ≤ endpointBound i U H := by
  unfold endpointBound
  split_ifs with he
  · subst i
    simpa [rowPrefix] using hU
  · apply le_min
    · apply (Nat.le_div_iff_mul_le hi).mpr
      simpa [Nat.mul_comm] using (prefix_last_mul_le μ hi).trans hU
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < i-1)).mpr
      have h := prefix_last_after_first μ hi
      have hx : (i-1)*μ.rowLen (i-1) ≤ U-H := by omega
      simpa [Nat.mul_comm] using hx

lemma prefix_intersection_hook (μ : YoungDiagram) {i j H W : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0)
    (hHp : 0 < H) (hWp : 0 < W) :
    min i W + min j H - 1 ≤
      ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card := by
  let A := (rectangle 1 (min i W)).cells
  let B := (rectangle (min j H) 1).cells
  have hA : A ⊆ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
    rintro ⟨a,b⟩ hp
    have hx : a < 1 ∧ b < min i W := mem_rectangle.mp hp
    have ha : a = 0 := by omega
    subst a
    have hc : (0,b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    simpa only [Finset.mem_inter,YoungDiagram.mem_cells,mem_rowTruncate,mem_colTruncate]
      using And.intro ⟨hc,hj⟩ ⟨hc,lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have hB : B ⊆ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
    rintro ⟨a,b⟩ hp
    have hx : a < min j H ∧ b < 1 := mem_rectangle.mp hp
    have hb : b = 0 := by omega
    subst b
    have hc : (a,0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    simpa only [Finset.mem_inter,YoungDiagram.mem_cells,mem_rowTruncate,mem_colTruncate]
      using And.intro ⟨hc,lt_of_lt_of_le hx.1 (min_le_left _ _)⟩ ⟨hc,hi⟩
  have hAB : A ∩ B = {(0,0)} := by
    ext ⟨a,b⟩
    simp only [Finset.mem_inter,Finset.mem_singleton,Prod.mk.injEq]
    simp only [A,B,rectangle,Finset.mem_product,Finset.mem_range]
    omega
  have he := Finset.card_union_add_card_inter A B
  have ha : A.card = min i W := by simp [A,rectangle]
  have hb : B.card = min j H := by simp [B,rectangle]
  rw [hAB,Finset.card_singleton,ha,hb] at he
  have h := Finset.card_le_card (Finset.union_subset hA hB)
  omega

def refinedArea (i j U V X Y H W : ℕ) : ℕ :=
  if j ≤ X ∧ i ≤ Y then
    max (U+V-(min i W + min j H - 1)) (U+V-i*j+(X-j)*(Y-i))
  else U+V-(min i W + min j H - 1)

lemma area_le_refined (μ : YoungDiagram) {i j U V X Y H W : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hU : colPrefix μ i ≤ U) (hV : rowPrefix μ j ≤ V)
    (hX : μ.colLen (i-1) ≤ X) (hY : μ.rowLen (j-1) ≤ Y)
    (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0) (hHp : 0 < H) (hWp : 0 < W) :
    μ.card ≤ refinedArea i j U V X Y H W := by
  classical
  have hid := strip_area_identity μ i j
  have hh := prefix_intersection_hook μ hi hj hH hW hHp hWp
  by_cases hcell : (j-1,i-1) ∈ μ
  · have heq : (rowTruncate μ j).cells ∩ (colTruncate μ i).cells =
        (rectangle j i).cells := by
      ext ⟨a,b⟩
      simp only [Finset.mem_inter, YoungDiagram.mem_cells, mem_rowTruncate,
        mem_colTruncate, mem_rectangle]
      constructor
      · tauto
      · rintro ⟨ha,hb⟩
        have hx := μ.up_left_mem (by omega : a ≤ j-1) (by omega : b ≤ i-1) hcell
        tauto
    have hint : ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card = j*i := by
      rw [heq]
      simp only [rectangle,Finset.card_product,Finset.card_range]
    have hcor := Finset.card_le_card (corner_subset_rectangle μ hi hj)
    simp only [Finset.card_product,Nat.card_Ico] at hcor
    have hmul := Nat.mul_le_mul (Nat.sub_le_sub_right hX j) (Nat.sub_le_sub_right hY i)
    have hx : j ≤ μ.colLen (i-1) := by
      have := YoungDiagram.mem_iff_lt_colLen.mp hcell; omega
    have hy : i ≤ μ.rowLen (j-1) := by
      have := YoungDiagram.mem_iff_lt_rowLen.mp hcell; omega
    rw [hint] at hid
    have hup : i*j ≤ U+V := by
      have ht := prefix_last_mul_le μ.transpose hi
      simp only [YoungDiagram.rowLen_transpose] at ht
      change i * μ.colLen (i-1) ≤ colPrefix μ i at ht
      nlinarith
    have hsub := Nat.sub_add_cancel hup
    have ha : μ.card ≤ U+V-i*j+(X-j)*(Y-i) := by
      rw [Nat.mul_comm j i] at hid
      omega
    unfold refinedArea
    rw [ite_eq_left ⟨hx.trans hX,hy.trans hY⟩]
    exact ha.trans (le_max_right _ _)
  · have hz : μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a,b⟩ hp
      simp only [Finset.mem_sdiff,Finset.mem_union,YoungDiagram.mem_cells,
        mem_rowTruncate,mem_colTruncate,not_or] at hp
      have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1,ha⟩
      have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1,hb⟩
      exact hcell (μ.up_left_mem (by omega) (by omega) hp.1)
    rw [hz,Finset.card_empty,add_zero] at hid
    have ha : μ.card ≤ U+V-(min i W+min j H-1) := by omega
    unfold refinedArea
    split_ifs
    · exact ha.trans (le_max_left _ _)
    · exact ha

end UniversalTensorSquare
end
end

end OAI
