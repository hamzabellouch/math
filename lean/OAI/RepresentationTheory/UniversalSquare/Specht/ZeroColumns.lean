import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ColumnReorder

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

theorem discard_zero_columns (rs : List ℕ) :
    ∃ e : Cells rs ≃ Cells (rs.filter (fun a => 0 < a)),
      (∀ c, row (e c) = row c) ∧
      (∀ c d, col (e c) = col (e d) ↔ col c = col d) := by
  induction rs with
  | nil => exact ⟨Equiv.refl _,fun c => isEmptyElim c,fun c => isEmptyElim c⟩
  | cons a rs ih =>
    obtain ⟨e,hr,hc⟩ := ih
    by_cases ha : 0 < a
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      refine ⟨(Equiv.refl (Fin a)).sumCongr e, ?_, ?_⟩
      · intro c
        rcases c with c | c
        · rfl
        · exact hr c
      · intro c d
        rcases c with c | c <;> rcases d with d | d
        · simp [col]
        · simp [col]
        · simp [col]
        · simpa only [Equiv.sumCongr_apply, Sum.map_inr, col, Nat.add_right_cancel_iff]
            using hc c d
    · have ha0 : a = 0 := by omega
      subst a
      rw [List.filter_cons_of_neg (by simp)]
      refine ⟨(Equiv.emptySum (Fin 0) (Cells rs)).trans e, ?_, ?_⟩
      · intro c
        rcases c with c | c
        · exact Fin.elim0 c
        · exact hr c
      · intro c d
        rcases c with c | c
        · exact Fin.elim0 c
        · rcases d with d | d
          · exact Fin.elim0 d
          · change (col (e c) = col (e d) ↔ col c + 1 = col d + 1)
            simpa only [Nat.add_right_cancel_iff] using hc c d

def positiveSorted (rs : List ℕ) : List ℕ :=
  (↑(rs.filter (fun a => 0 < a)) : Multiset ℕ).sort (· ≥ ·)

lemma positiveSorted_perm (rs : List ℕ) :
    (rs.filter (fun a => 0 < a)).Perm (positiveSorted rs) := by
  apply Multiset.coe_eq_coe.mp
  simp only [positiveSorted, Multiset.sort_eq]

lemma positiveSorted_sorted (rs : List ℕ) : (positiveSorted rs).SortedGE :=
  (Multiset.pairwise_sort _ _).sortedGE

lemma positiveSorted_pos (rs : List ℕ) (a : ℕ) (ha : a ∈ positiveSorted rs) : 0 < a := by
  have hm := (positiveSorted_perm rs).mem_iff.mpr ha
  exact of_decide_eq_true (List.mem_filter.mp hm).2

def columnShape (rs : List ℕ) : YoungDiagram :=
  (YoungDiagram.ofRowLens (positiveSorted rs) (positiveSorted_sorted rs)).transpose

lemma columnShape_cols (rs : List ℕ) :
    (columnShape rs).transpose.rowLens = positiveSorted rs := by
  simp only [columnShape, YoungDiagram.transpose_transpose]
  exact YoungDiagram.rowLens_ofRowLens_eq_self (positiveSorted_pos rs)

theorem columnShape_placement (rs : List ℕ) :
    ∃ e : Cells rs ≃ (columnShape rs).cells,
      (∀ c, (e c).val.1 = row c) ∧
      (∀ c d, (e c).val.2 = (e d).val.2 ↔ col c = col d) := by
  obtain ⟨e,hr,hc⟩ := discard_zero_columns rs
  obtain ⟨f,hr',hc'⟩ := place_columns (columnShape rs)
    ((positiveSorted_perm rs).trans (by rw [columnShape_cols]))
  refine ⟨e.trans f,fun c => (hr' (e c)).trans (hr c),fun c d => ?_⟩
  exact (hc' (e c) (e d)).trans (hc c d)

lemma placed_card {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells) :
    μ.card = rs.sum := by
  have h := Fintype.card_congr ((enumerate rs).trans e)
  simpa only [Fintype.card_fin, Fintype.card_coe, YoungDiagram.card] using h.symm

lemma columnShape_card (rs : List ℕ) : (columnShape rs).card = rs.sum := by
  obtain ⟨e,_,_⟩ := columnShape_placement rs
  exact placed_card e

lemma row_lt_some_height {rs : List ℕ} (c : Cells rs) :
    ∃ h ∈ rs, row c < h := by
  induction rs with
  | nil => exact isEmptyElim c
  | cons h rs ih =>
    rcases c with c | c
    · exact ⟨h,by simp,c.isLt⟩
    · obtain ⟨h,hh,hc⟩ := ih c
      exact ⟨h,List.mem_cons_of_mem _ hh,hc⟩

lemma placed_height {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (B : ℕ) (hB : ∀ h ∈ rs, h ≤ B) :
    μ.colLen 0 ≤ B := by
  by_contra hh
  let x : μ.cells := ⟨(B,0),YoungDiagram.mem_iff_lt_colLen.mpr (by omega)⟩
  obtain ⟨h,hh,hc⟩ := row_lt_some_height (e.symm x)
  have ha := hr (e.symm x)
  rw [Equiv.apply_symm_apply] at ha
  change B = row (e.symm x) at ha
  have hb := hB h hh
  omega

lemma columnShape_height (rs : List ℕ) (B : ℕ) (hB : ∀ h ∈ rs, h ≤ B) :
    (columnShape rs).colLen 0 ≤ B := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_height e hr B hB

lemma sum_fin_val_ite (r i : ℕ) :
    (∑ j : Fin r, if j.val = i then (1:ℕ) else 0) = if i < r then 1 else 0 := by
  classical
  by_cases hi : i < r
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin r)]
    · simp
    · intro j hj hji
      exact ite_eq_right (fun h => hji (Fin.ext h))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h : (j : ℕ) = i => hi (h ▸ j.isLt))

lemma cells_row_count (rs : List ℕ) (i : ℕ) :
    (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) = rs.countP (fun h => i < h) := by
  classical
  induction rs with
  | nil => simp [Cells]
  | cons h rs ih =>
    rw [show (∑ c : Cells (h :: rs), if row c = i then (1:ℕ) else 0) =
      (∑ c : Fin h, if c.val = i then (1:ℕ) else 0) +
        (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) from
      Fintype.sum_sum_type _]
    rw [sum_fin_val_ite, ih, List.countP_cons]
    split_ifs <;> simp_all <;> omega

def rowFiberEquiv (μ : YoungDiagram) (i : ℕ) :
    {c : μ.cells // c.val.1 = i} ≃ Fin (μ.rowLen i) where
  toFun c := ⟨c.val.val.2,YoungDiagram.mem_iff_lt_rowLen.mp (by
    have hc : (c.val.val.1,c.val.val.2) ∈ μ := c.val.property
    rwa [c.property] at hc)⟩
  invFun j := ⟨⟨(i,j.val),YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩,rfl⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext c.property.symm rfl
  right_inv j := by rfl

lemma placed_rowLen {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (i : ℕ) :
    μ.rowLen i = rs.countP (fun h => i < h) := by
  classical
  let E : {c : Cells rs // row c = i} ≃ {c : μ.cells // c.val.1 = i} :=
    e.subtypeEquiv (fun c => by rw [hr])
  have hc := Fintype.card_congr (E.trans (rowFiberEquiv μ i))
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter, cells_row_count] at hc
  exact hc.symm

lemma columnShape_rowLen (rs : List ℕ) (i : ℕ) :
    (columnShape rs).rowLen i = rs.countP (fun h => i < h) := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_rowLen e hr i

end Saxl.Columns
end
end

end OAI
