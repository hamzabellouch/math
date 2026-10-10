import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.BandAllocation
import OAI.RepresentationTheory.UniversalSquare.Specht.ColumnClearance

namespace OAI

/-! Band Allocation Lists. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma colLen_pos_iff (μ : YoungDiagram) (i : ℕ) :
    0 < μ.colLen i ↔ i < μ.rowLen 0 := by
  rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen]

lemma positive_column_list (μ : YoungDiagram) (W : ℕ) (hW : μ.rowLen 0 ≤ W) :
    ((List.range W).map μ.colLen).filter (fun a => 0 < a) = μ.transpose.rowLens := by
  rw [List.filter_map]
  have h : (List.range W).filter ((fun a => decide (0 < a)) ∘ μ.colLen) =
      List.range (μ.rowLen 0) := by
    calc _ = (List.range W).filter (fun i => decide (i < μ.rowLen 0)) := by
           apply List.filter_congr
           intro i hi
           simp only [Function.comp_apply, colLen_pos_iff]
         _ = List.range (μ.rowLen 0) := by
           rw [← List.Ico.zero_bot W, List.Ico.filter_lt_of_ge hW, List.Ico.zero_bot]
  rw [h]
  simp only [YoungDiagram.rowLens, YoungDiagram.colLen_transpose]
  apply List.map_congr_left
  intro i hi
  exact (YoungDiagram.rowLen_transpose μ i).symm

lemma column_list_sum (μ : YoungDiagram) (W : ℕ) (hW : μ.rowLen 0 ≤ W) :
    ((List.range W).map μ.colLen).sum = μ.card := by
  rw [← List.sum_toFinset μ.colLen List.nodup_range]
  simpa only [List.toFinset_range, rowPrefix, YoungDiagram.rowLen_transpose, transpose_card]
    using rowPrefix_eq_card μ.transpose (by simpa using hW)

lemma place_padded_columns (μ : YoungDiagram) (W : ℕ) (hW : μ.rowLen 0 ≤ W)
    (rs : List ℕ) (h : rs.Perm ((List.range W).map μ.colLen)) :
    ∃ e : Columns.Cells rs ≃ μ.cells,
      (∀ c, (e c).val.1 = Columns.row c) ∧
      (∀ c d, (e c).val.2 = (e d).val.2 ↔ Columns.col c = Columns.col d) := by
  obtain ⟨e,hr,hc⟩ := Columns.discard_zero_columns rs
  have hh := h.filter (fun a => decide (0 < a))
  rw [positive_column_list μ W hW] at hh
  obtain ⟨f,hr',hc'⟩ := Columns.place_columns μ hh
  exact ⟨e.trans f,fun c => (hr' (e c)).trans (hr c),
    fun c d => (hc' (e c) (e d)).trans (hc c d)⟩

lemma width_le_of_cols {π μ : YoungDiagram} (h : ∀ i, π.colLen i ≤ μ.colLen i) :
    π.rowLen 0 ≤ μ.rowLen 0 := by
  by_contra hh
  have hi : 0 < π.colLen (μ.rowLen 0) := (colLen_pos_iff _ _).mpr (by omega)
  have hi' : 0 < μ.colLen (μ.rowLen 0) := hi.trans_le (h _)
  exact Nat.lt_irrefl _ ((colLen_pos_iff _ _).mp hi')

theorem band_subdiagram_columns (lam : YoungDiagram) (K r d q : ℕ)
    (hd : 1 ≤ d) (hK : K ≤ rowPrefix lam d) (hclear : d*q+7+d ≤ K)
    (hr : r ≤ bandCapacity lam d q) :
    ∃ μ η : YoungDiagram, ∃ ps : List (ℕ × ℕ),
      μ ≤ lam ∧ μ.card = K+2*r ∧ η.card = 2*r ∧
      (ps.map Prod.fst).sum = K ∧ (ps.map Prod.snd).sum = 2*r ∧
      (∀ p ∈ ps, 1 ≤ p.1 ∧ p.1 ≤ d) ∧
      (∀ p ∈ ps, p.2 ≠ 0 → p.1 = d) ∧
      Saxl.FlagColumns.columnsAway K ps 0 ∧
      (∀ i, Even (η.colLen i)) ∧ η.rowLen 0 ≤ q ∧
      (∃ e : Columns.Cells (ps.map (fun p => p.1+p.2)) ≃ μ.cells,
        (∀ c, (e c).val.1 = Columns.row c) ∧
        (∀ c c', (e c).val.2 = (e c').val.2 ↔ Columns.col c = Columns.col c')) ∧
      (∃ e : Columns.Cells (ps.map Prod.snd) ≃ η.cells,
        (∀ c, (e c).val.1 = Columns.row c) ∧
        (∀ c c', (e c).val.2 = (e c').val.2 ↔ Columns.col c = Columns.col c')) := by
  obtain ⟨π,η,μ,hμlam,hπcard,hηcard,hμcard,hcolsh,hplen,heven,hηw,hchosen⟩ :=
    band_subdiagram_allocation lam K r d q hK hclear hr
  let W := μ.rowLen 0
  let ps := (List.range W).map (fun i => (π.colLen i, η.colLen i))
  have hπw : π.rowLen 0 ≤ W := width_le_of_cols (fun i => by rw [hcolsh]; omega)
  have hηw' : η.rowLen 0 ≤ W := width_le_of_cols (fun i => by rw [hcolsh]; omega)
  have hs₁ : (ps.map Prod.fst).sum = K := by
    simpa only [ps,List.map_map,Function.comp_def] using
      (column_list_sum π W hπw).trans hπcard
  have hs₂ : (ps.map Prod.snd).sum = 2*r := by
    simpa only [ps,List.map_map,Function.comp_def] using
      (column_list_sum η W hηw').trans hηcard
  have ha : ∀ p ∈ ps, 1 ≤ p.1 ∧ p.1 ≤ d := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hm : 0 < μ.colLen i := (colLen_pos_iff μ i).mpr (List.mem_range.mp hi)
    rw [hcolsh] at hm
    by_cases he : 0 < η.colLen i
    · exact ⟨by rw [hchosen i he]; exact hd,hplen i⟩
    · exact ⟨by omega,hplen i⟩
  have hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d := by
    intro p hp hn
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    exact hchosen i (Nat.pos_of_ne_zero hn)
  have hlen : (ps.filter (fun p => p.2 ≠ 0)).length ≤ q := by
    have hh : (ps.filter (fun p => p.2 ≠ 0)).length = η.rowLen 0 := by
      dsimp only [ps]
      rw [List.filter_map, List.length_map]
      have hh : (List.range W).filter ((fun p : ℕ × ℕ => decide (p.2 ≠ 0)) ∘
          (fun i => (π.colLen i,η.colLen i))) = List.range (η.rowLen 0) := by
        calc _ = (List.range W).filter (fun i => decide (i < η.rowLen 0)) := by
               apply List.filter_congr
               intro i hi
               simp only [Function.comp_apply, Nat.pos_iff_ne_zero.symm, colLen_pos_iff]
             _ = List.range (η.rowLen 0) := by
               rw [← List.Ico.zero_bot W,List.Ico.filter_lt_of_ge hηw',List.Ico.zero_bot]
      rw [hh,List.length_range]
    exact hh.le.trans hηw
  obtain ⟨qs,hqs,hqc⟩ := Saxl.FlagColumns.reorder_columns_away ps d K q hs₁
    (fun p hp => (ha p hp).2) hb hlen hclear
  refine ⟨μ,η,qs,hμlam,hμcard,hηcard,(hqs.map Prod.fst).sum_eq.trans hs₁,
    (hqs.map Prod.snd).sum_eq.trans hs₂,
    fun p hp => ha p (hqs.mem_iff.mp hp),fun p hp => hb p (hqs.mem_iff.mp hp),
    hqc,heven,hηw,?_,?_⟩
  · apply place_padded_columns μ W le_rfl
    have hh := hqs.map (fun p => p.1+p.2)
    simpa only [ps,List.map_map,Function.comp_def,← hcolsh] using hh
  · apply place_padded_columns η W hηw'
    simpa only [ps,List.map_map,Function.comp_def] using hqs.map Prod.snd

end UniversalTensorSquare
end
end

end OAI
