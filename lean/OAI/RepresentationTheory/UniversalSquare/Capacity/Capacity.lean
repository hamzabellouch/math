import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.Candidate
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Capacity. -/

section

noncomputable section

namespace UniversalTensorSquare

open Saxl

def colPrefix (μ : YoungDiagram) (i : ℕ) : ℕ := rowPrefix μ.transpose i

lemma colPrefix_eq_sum (μ : YoungDiagram) (i : ℕ) :
    colPrefix μ i = ∑ k ∈ Finset.range i, μ.colLen k := by
  simp only [colPrefix, rowPrefix, YoungDiagram.rowLen_transpose]

lemma mem_colTruncate (μ : YoungDiagram) (i : ℕ) (a b : ℕ) :
    (a,b) ∈ colTruncate μ i ↔ (a,b) ∈ μ ∧ b < i := by
  simp only [colTruncate, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    Saxl.mem_rowTruncate]

lemma rowTruncate_subset (μ : YoungDiagram) (j : ℕ) :
    (rowTruncate μ j).cells ⊆ μ.cells := by
  intro p hp
  exact (Saxl.mem_rowTruncate.mp hp).1

lemma colTruncate_subset (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).cells ⊆ μ.cells := by
  rintro ⟨a,b⟩ hp
  exact ((mem_colTruncate μ i a b).mp hp).1

lemma colTruncate_card (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).card = colPrefix μ i := by
  rw [colTruncate, Saxl.transpose_card, rowTruncate_card, colPrefix]

lemma strip_area_identity (μ : YoungDiagram) (i j : ℕ) :
    μ.card + ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card =
      rowPrefix μ j + colPrefix μ i +
        (μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells)).card := by
  have hu : (rowTruncate μ j).cells ∪ (colTruncate μ i).cells ⊆ μ.cells :=
    Finset.union_subset (rowTruncate_subset μ j) (colTruncate_subset μ i)
  have h₁ := Finset.card_sdiff_add_card_eq_card hu
  have h₂ := Finset.card_union_add_card_inter
    (rowTruncate μ j).cells (colTruncate μ i).cells
  have h₃ := rowTruncate_card μ j
  have h₄ := colTruncate_card μ i
  change (rowTruncate μ j).cells.card = _ at h₃
  change (colTruncate μ i).cells.card = _ at h₄
  change μ.cells.card + _ = _
  omega

lemma corner_subset_rectangle (μ : YoungDiagram) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) ⊆
      Finset.Ico j (μ.colLen (i-1)) ×ˢ Finset.Ico i (μ.rowLen (j-1)) := by
  rintro ⟨a,b⟩ hp
  simp only [Finset.mem_sdiff, Finset.mem_union, YoungDiagram.mem_cells,
    mem_rowTruncate, mem_colTruncate, not_or] at hp
  have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1, ha⟩
  have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1, hb⟩
  have ha' : a < μ.colLen (i-1) := YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (by omega) hp.1)
  have hb' : b < μ.rowLen (j-1) := YoungDiagram.mem_iff_lt_rowLen.mp
    (μ.up_left_mem (by omega) le_rfl hp.1)
  simpa only [Finset.mem_product, Finset.mem_Ico] using And.intro ⟨ha, ha'⟩ ⟨hb,hb'⟩

lemma prefix_last_mul_le (μ : YoungDiagram) {j : ℕ} (hj : 0 < j) :
    j * μ.rowLen (j-1) ≤ rowPrefix μ j := by
  have h := Finset.sum_le_sum (s := Finset.range j) (f := fun _ => μ.rowLen (j-1))
    (g := fun a => μ.rowLen a) (by
      intro a ha
      exact μ.rowLen_anti a (j-1) (by have := Finset.mem_range.mp ha; omega))
  simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, rowPrefix] using h

theorem capacity_rectangle (μ : YoungDiagram) {i j U V : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hU : colPrefix μ i ≤ U) (hV : rowPrefix μ j ≤ V) :
    μ.card ≤ max (U+V-1) (U*V/(i*j)) := by
  classical
  by_cases hcell : (j-1,i-1) ∈ μ
  · have heq : (rowTruncate μ j).cells ∩ (colTruncate μ i).cells =
        (rectangle j i).cells := by
      ext ⟨a,b⟩
      simp only [Finset.mem_inter, YoungDiagram.mem_cells, Saxl.mem_rowTruncate,
        mem_colTruncate, mem_rectangle]
      constructor
      · tauto
      · rintro ⟨ha,hb⟩
        have hx := μ.up_left_mem (by omega : a ≤ j-1) (by omega : b ≤ i-1) hcell
        tauto
    have hint : ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card = j*i := by
      rw [heq]
      simp only [rectangle, Finset.card_product, Finset.card_range]
    have hcorner := Finset.card_le_card (corner_subset_rectangle μ hi hj)
    simp only [Finset.card_product, Nat.card_Ico] at hcorner
    have hid := strip_area_identity μ i j
    rw [hint, Nat.mul_comm j i] at hid
    have harea : μ.card + i*j ≤ U+V + (μ.colLen (i-1)-j)*(μ.rowLen (j-1)-i) := by
      omega
    have hx : j ≤ μ.colLen (i-1) := by
      have := YoungDiagram.mem_iff_lt_colLen.mp hcell
      omega
    have hy : i ≤ μ.rowLen (j-1) := by
      have := YoungDiagram.mem_iff_lt_rowLen.mp hcell
      omega
    have hxu : i*μ.colLen (i-1) ≤ U := by
      simpa only [YoungDiagram.rowLen_transpose] using
        (prefix_last_mul_le μ.transpose hi).trans hU
    have hyv : j*μ.rowLen (j-1) ≤ V := (prefix_last_mul_le μ hj).trans hV
    have hu : i*j ≤ U := (Nat.mul_le_mul_left i hx).trans hxu
    have hv : i*j ≤ V := by nlinarith
    have ha : i*(μ.colLen (i-1)-j) ≤ U-i*j := by
      rw [Nat.mul_sub_left_distrib]
      exact Nat.sub_le_sub_right hxu _
    have hb : j*(μ.rowLen (j-1)-i) ≤ V-i*j := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_comm j i]
      exact Nat.sub_le_sub_right hyv _
    have hprod := Nat.mul_le_mul ha hb
    have hscaled := Nat.mul_le_mul_left (i*j) harea
    have hmul : μ.card * (i*j) ≤ U*V := by
      have hU' := Nat.sub_add_cancel hu
      have hV' := Nat.sub_add_cancel hv
      nlinarith
    exact (Nat.le_div_iff_mul_le (Nat.mul_pos hi hj)).mpr hmul |>.trans (le_max_right _ _)
  · have hcorner : μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a,b⟩ hp
      simp only [Finset.mem_sdiff, Finset.mem_union, YoungDiagram.mem_cells,
        mem_rowTruncate, mem_colTruncate, not_or] at hp
      have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1, ha⟩
      have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1, hb⟩
      exact hcell (μ.up_left_mem (by omega) (by omega) hp.1)
    by_cases hn : μ.card = 0
    · simp [hn]
    have hzero : (0,0) ∈ μ := by
      obtain ⟨⟨a,b⟩,hp⟩ := Finset.card_pos.mp (show 0 < μ.cells.card from Nat.pos_of_ne_zero hn)
      exact μ.up_left_mem (Nat.zero_le _) (Nat.zero_le _) hp
    have hzmem : (0,0) ∈ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
      simpa only [Finset.mem_inter, YoungDiagram.mem_cells, mem_rowTruncate,
        mem_colTruncate, and_self] using And.intro ⟨hzero,hj⟩ ⟨hzero,hi⟩
    have hpos := Finset.card_pos.mpr ⟨(0,0),hzmem⟩
    have hid := strip_area_identity μ i j
    rw [hcorner, Finset.card_empty, add_zero] at hid
    exact (show μ.card ≤ U+V-1 by omega).trans (le_max_left _ _)

def bandCapacity (μ : YoungDiagram) (d q : ℕ) : ℕ :=
  ∑ k ∈ Finset.range q, (μ.colLen k - d) / 2

def BandTest (M r : ℕ) (μ : YoungDiagram) : Prop :=
  ∃ d, 1 ≤ d ∧ d ≤ 4 ∧ ∃ q, q ≤ 8 ∧
    2*M-1 ≤ rowPrefix μ d ∧ d*q+7+d ≤ 2*M-1 ∧ r ≤ bandCapacity μ d q

lemma capacity_floor_bound (x f : ℕ) : x ≤ 2*((x-f)/2)+f+1 := by omega

lemma prefix_le_capacity (μ : YoungDiagram) (d q : ℕ) :
    colPrefix μ q ≤ 2*bandCapacity μ d q + q*(d+1) := by
  rw [colPrefix_eq_sum, bandCapacity]
  have h := Finset.sum_le_sum (s := Finset.range q)
    (fun k _ => capacity_floor_bound (μ.colLen k) d)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_add, Nat.mul_one,
    Nat.add_assoc] using h

lemma capacity_large_numeric (M r n : ℕ) (hM : 22 ≤ M) (hr : 2*r ≤ 3*M+4)
    (hn : 2*n = M*(M+1)+4*r) :
    2*(2*r+38) < n ∧ (2*r+38)*(2*r+38) < 64*n := by
  have hM2 := Nat.mul_le_mul_left M hM
  have hr2 := Nat.mul_le_mul hr hr
  constructor <;> nlinarith

theorem capacity_large (μ : YoungDiagram) (M r : ℕ) (hM : 22 ≤ M)
    (hr : 2*r ≤ 3*M+4)
    (hn : μ.card = (staircase M).card + 2*r)
    (hH : 2*M-1 ≤ colPrefix μ 4) (hW : 2*M-1 ≤ rowPrefix μ 4) :
    BandTest M r μ ∨ BandTest M r μ.transpose := by
  classical
  by_contra hh
  push Not at hh
  have ha : (4:ℕ)*8+7+4 ≤ 2*M-1 := by omega
  have hc : bandCapacity μ 4 8 < r := by
    by_contra hc
    exact hh.1 ⟨4, by omega, by omega, 8, by omega, hW, ha, by omega⟩
  have hct : bandCapacity μ.transpose 4 8 < r := by
    by_contra hc
    exact hh.2 ⟨4, by omega, by omega, 8, by omega, hH, ha, by omega⟩
  have h₁ : colPrefix μ 8 ≤ 2*r+38 := by
    have := prefix_le_capacity μ 4 8
    omega
  have h₂ : rowPrefix μ 8 ≤ 2*r+38 := by
    have hp := prefix_le_capacity μ.transpose 4 8
    simp only [colPrefix, YoungDiagram.transpose_transpose] at hp
    omega
  have hb := capacity_rectangle μ (by omega : 0 < 8) (by omega : 0 < 8) h₁ h₂
  have he : 2*μ.card = M*(M+1)+4*r := by
    have hx := staircase_card_double M
    nlinarith
  obtain ⟨hl,hu⟩ := capacity_large_numeric M r μ.card hM hr he
  have hdiv : (2*r+38)*(2*r+38)/(8*8) < μ.card := by
    exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by nlinarith)
  have hmax : max (2*r+38+(2*r+38)-1) ((2*r+38)*(2*r+38)/(8*8)) < μ.card :=
    max_lt (by omega) hdiv
  omega

end UniversalTensorSquare
end
end

end OAI
