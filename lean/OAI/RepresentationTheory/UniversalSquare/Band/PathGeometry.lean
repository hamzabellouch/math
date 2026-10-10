import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.Candidate
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Path Geometry. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

def candidatePathCell (M b δ : ℕ) (q : Fin (2*M-1)) : ℕ × ℕ :=
  if q.val = 0 then (M+b+δ-1,0) else
  if q.val = 2*M-2 then (0,M+b+δ-1) else
    (M-1-(q.val+1)/2, q.val/2)

def attachmentNE (M b δ : ℕ) : Finset (ℕ × ℕ) :=
  {0} ×ˢ Finset.Ico (M-1) (M+b+δ-1) ∪
    {1} ×ˢ Finset.Ico (M-1) (M+b-1)

lemma mem_attachmentNE {M b δ i j : ℕ} :
    (i,j) ∈ attachmentNE M b δ ↔
      (i = 0 ∧ M-1 ≤ j ∧ j < M+b+δ-1) ∨
      (i = 1 ∧ M-1 ≤ j ∧ j < M+b-1) := by
  simp only [attachmentNE, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Ico]

lemma attachmentNE_card (M b δ : ℕ) (hM : 1 ≤ M) :
    (attachmentNE M b δ).card = 2*b+δ := by
  unfold attachmentNE
  rw [Finset.card_union_of_disjoint]
  · simp only [Finset.card_product, Finset.card_singleton, Nat.card_Ico, one_mul]
    omega
  · apply Finset.disjoint_left.mpr
    rintro ⟨i,j⟩ hi hj
    simp only [Finset.mem_product, Finset.mem_singleton] at hi hj
    omega

lemma candidatePathCell_mem (M b δ : ℕ) (hM : 4 ≤ M) (q : Fin (2*M-1)) :
    candidatePathCell M b δ q ∈ candidate M b δ ∧
      M-2 ≤ (candidatePathCell M b δ q).1 + (candidatePathCell M b δ q).2 := by
  have hq := q.isLt
  unfold candidatePathCell
  split_ifs with h₀ h₁
  · simp only [ add_zero, mem_candidate]
    omega
  · simp only [ zero_add, mem_candidate]
    omega
  · simp only [ mem_candidate]
    omega

lemma candidatePathCell_injective (M b δ : ℕ) (hM : 4 ≤ M) :
    Function.Injective (candidatePathCell M b δ) := by
  intro q t he
  have hq := q.isLt
  have ht := t.isLt
  apply Fin.ext
  unfold candidatePathCell at he
  split_ifs at he <;> simp only [Prod.mk.injEq] at he <;> omega

lemma pathCell_not_attachment (M b δ : ℕ) (hM : 4 ≤ M) (q : Fin (2*M-1)) :
    candidatePathCell M b δ q ∉ attachmentNE M b δ ∧
      (candidatePathCell M b δ q).swap ∉ attachmentNE M b δ := by
  have hq := q.isLt
  unfold candidatePathCell
  split_ifs <;> simp only [Prod.swap_prod_mk, mem_attachmentNE] <;> omega

lemma attachment_disjoint_transpose (M b δ : ℕ) (hM : 4 ≤ M) :
    Disjoint (attachmentNE M b δ)
      ((attachmentNE M b δ).map (Equiv.prodComm ℕ ℕ).toEmbedding) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i,j⟩ hi hj
  simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk, mem_attachmentNE] at hi hj
  omega

lemma attachmentNE_mem (M b δ : ℕ) (hM : 4 ≤ M) {i j : ℕ}
    (hx : (i,j) ∈ attachmentNE M b δ) :
    (i,j) ∈ candidate M b δ ∧ M-2 ≤ i+j := by
  rw [mem_attachmentNE] at hx
  rw [mem_candidate]
  omega

lemma candidate_band_indices (M b δ : ℕ) (hM : 4 ≤ M) (i j : ℕ)
    (hc : (i,j) ∈ candidate M b δ) (ht : M-2 ≤ i+j)
    (hne : (i,j) ∉ attachmentNE M b δ) (hsw : (j,i) ∉ attachmentNE M b δ)
    (h₀ : ¬ (j = 0 ∧ i = M+b+δ-1)) (h₁ : ¬ (i = 0 ∧ j = M+b+δ-1)) :
    i+j = M-2 ∨ (i+j = M-1 ∧ 0 < i ∧ 0 < j) := by
  rw [mem_candidate] at hc
  rw [mem_attachmentNE] at hne hsw
  omega

lemma candidatePathCell_odd (M b δ : ℕ) (hM : 4 ≤ M) (i j : ℕ)
    (hs : i+j = M-2) :
    ∃ q : Fin (2*M-1), candidatePathCell M b δ q = (i,j) := by
  refine ⟨⟨2*j+1,by omega⟩, ?_⟩
  simp only [candidatePathCell]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  apply Prod.ext <;> dsimp only <;> omega

lemma candidatePathCell_even (M b δ : ℕ) (hM : 4 ≤ M) (i j : ℕ)
    (hs : i+j = M-1) (hi : 0 < i) (hj : 0 < j) :
    ∃ q : Fin (2*M-1), candidatePathCell M b δ q = (i,j) := by
  refine ⟨⟨2*j,by omega⟩, ?_⟩
  simp only [candidatePathCell]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  apply Prod.ext <;> dsimp only <;> omega

theorem candidate_band_cell_decomposition (M b δ : ℕ) (hM : 4 ≤ M) (i j : ℕ)
    (hc : (i,j) ∈ candidate M b δ) (ht : M-2 ≤ i+j) :
    (∃ q : Fin (2*M-1), candidatePathCell M b δ q = (i,j)) ∨
      (i,j) ∈ attachmentNE M b δ ∨ (j,i) ∈ attachmentNE M b δ := by
  by_cases hne : (i,j) ∈ attachmentNE M b δ
  · exact Or.inr (Or.inl hne)
  by_cases hsw : (j,i) ∈ attachmentNE M b δ
  · exact Or.inr (Or.inr hsw)
  apply Or.inl
  by_cases h₀ : j = 0 ∧ i = M+b+δ-1
  · refine ⟨⟨0,by omega⟩, ?_⟩
    simp only [candidatePathCell, ite_true]
    exact Prod.ext (by omega) (by omega)
  by_cases h₁ : i = 0 ∧ j = M+b+δ-1
  · refine ⟨⟨2*M-2,by omega⟩, ?_⟩
    simp only [candidatePathCell, ite_eq_right (show 2*M-2 ≠ 0 by omega), ite_true]
    exact Prod.ext (by omega) (by omega)
  rcases candidate_band_indices M b δ hM i j hc ht hne hsw h₀ h₁ with hs | ⟨hs,hi,hj⟩
  · exact candidatePathCell_odd M b δ hM i j hs
  · exact candidatePathCell_even M b δ hM i j hs hi hj

theorem candidate_band_cells (M b δ : ℕ) (hM : 4 ≤ M) :
    (candidate M b δ).cells \ (staircase (M-2)).cells =
      Finset.univ.image (candidatePathCell M b δ) ∪ attachmentNE M b δ ∪
        (attachmentNE M b δ).map (Equiv.prodComm ℕ ℕ).toEmbedding := by
  ext ⟨i,j⟩
  simp only [Finset.mem_sdiff, YoungDiagram.mem_cells, mem_staircase, not_lt,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk]
  constructor
  · rintro ⟨hc,ht⟩
    exact (or_assoc).mpr (candidate_band_cell_decomposition M b δ hM i j hc ht)
  · rintro ((⟨q,hq⟩ | hn) | hs)
    · have h := candidatePathCell_mem M b δ hM q
      simpa only [hq] using h
    · exact attachmentNE_mem M b δ hM hn
    · have h := attachmentNE_mem M b δ hM hs
      constructor
      · have hx : (i,j) ∈ (candidate M b δ).transpose := by
          simpa only [YoungDiagram.mem_transpose, Prod.swap_prod_mk] using h.1
        simpa only [candidate_transpose] using hx
      · omega

theorem path_endpoint_clearance (M b δ : ℕ) (hM : 4 ≤ M)
    (q : Fin (2*M-1)) (hle : 4 ≤ q.val) (hri : q.val+4 < 2*M-1) :
    2 ≤ (candidatePathCell M b δ q).1 ∧
      2 ≤ (candidatePathCell M b δ q).2 := by
  simp only [candidatePathCell]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  dsimp only
  omega

end UniversalTensorSquare
end
end

end OAI
