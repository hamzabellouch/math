import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.Extensions

namespace OAI

/-! Candidate. -/

section

noncomputable section
namespace UniversalTensorSquare

def rectangle (a b : ℕ) : YoungDiagram where
  cells := Finset.range a ×ˢ Finset.range b
  isLowerSet := by
    intro x y hxy hy
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at hy ⊢
    exact ⟨lt_of_le_of_lt hxy.1 hy.1, lt_of_le_of_lt hxy.2 hy.2⟩

@[simp] lemma mem_rectangle {a b i j : ℕ} :
    (i, j) ∈ rectangle a b ↔ i < a ∧ j < b := by
  change (i, j) ∈ Finset.range a ×ˢ Finset.range b ↔ _
  simp

def candidateArm (M b δ : ℕ) : YoungDiagram :=
  rectangle 1 (M + b + δ) ⊔ rectangle 2 (M - 1 + b)

def candidate (M b δ : ℕ) : YoungDiagram :=
  Saxl.staircase M ⊔ candidateArm M b δ ⊔ (candidateArm M b δ).transpose

lemma mem_candidate {M b δ i j : ℕ} :
    (i, j) ∈ candidate M b δ ↔
      i + j < M ∨
      (i < 1 ∧ j < M + b + δ) ∨ (i < 2 ∧ j < M - 1 + b) ∨
      (j < 1 ∧ i < M + b + δ) ∨ (j < 2 ∧ i < M - 1 + b) := by
  simp only [candidate, candidateArm, YoungDiagram.mem_sup, Saxl.mem_staircase,
    mem_rectangle, YoungDiagram.mem_transpose, Prod.swap_prod_mk]
  tauto

@[simp] lemma candidate_transpose (M b δ : ℕ) :
    (candidate M b δ).transpose = candidate M b δ := by
  apply SetLike.ext
  rintro ⟨i, j⟩
  simp only [YoungDiagram.mem_transpose, Prod.swap_prod_mk, mem_candidate]
  omega

def armExtras (M b δ : ℕ) : Finset (ℕ × ℕ) :=
  {0} ×ˢ Finset.Ico M (M + b + δ) ∪
    {1} ×ˢ Finset.Ico (M - 1) (M - 1 + b)

lemma mem_armExtras {M b δ i j : ℕ} :
    (i, j) ∈ armExtras M b δ ↔
      (i = 0 ∧ M ≤ j ∧ j < M + b + δ) ∨
      (i = 1 ∧ M - 1 ≤ j ∧ j < M - 1 + b) := by
  simp only [armExtras, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico]

lemma armExtras_card (M b δ : ℕ) : (armExtras M b δ).card = 2 * b + δ := by
  unfold armExtras
  rw [Finset.card_union_of_disjoint]
  · simp only [Finset.card_product, Finset.card_singleton, Nat.card_Ico, one_mul]
    omega
  · apply Finset.disjoint_left.mpr
    rintro ⟨i, j⟩ hi hj
    simp only [Finset.mem_product, Finset.mem_singleton] at hi hj
    omega

lemma staircase_disjoint_armExtras (M b δ : ℕ) (hM : 1 ≤ M) :
    Disjoint (Saxl.staircase M).cells (armExtras M b δ) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i, j⟩ hi hj
  simp only [YoungDiagram.mem_cells, Saxl.mem_staircase] at hi
  rw [mem_armExtras] at hj
  omega

lemma armExtras_disjoint_transpose (M b δ : ℕ) (hM : 3 ≤ M) :
    Disjoint (armExtras M b δ)
      ((armExtras M b δ).map (Equiv.prodComm ℕ ℕ).toEmbedding) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i, j⟩ hi hj
  simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk] at hj
  simp only [mem_armExtras] at hi hj
  omega

lemma candidate_cells (M b δ : ℕ) (hM : 1 ≤ M) :
    (candidate M b δ).cells =
      (Saxl.staircase M).cells ∪ armExtras M b δ ∪
        (armExtras M b δ).map (Equiv.prodComm ℕ ℕ).toEmbedding := by
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_candidate, Finset.mem_union,
    Saxl.mem_staircase, mem_armExtras, Finset.mem_map_equiv,
    Equiv.prodComm_symm, Equiv.prodComm_apply,
    Prod.swap_prod_mk]
  omega

lemma candidate_card (M b δ : ℕ) (hM : 3 ≤ M) :
    (candidate M b δ).card = (Saxl.staircase M).card + 4 * b + 2 * δ := by
  change (candidate M b δ).cells.card = _
  rw [candidate_cells M b δ (by omega)]
  have hd : Disjoint (Saxl.staircase M).cells
      ((armExtras M b δ).map (Equiv.prodComm ℕ ℕ).toEmbedding) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨i, j⟩ hi hj
    simp only [YoungDiagram.mem_cells, Saxl.mem_staircase] at hi
    simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply,
      Prod.swap_prod_mk, mem_armExtras] at hj
    omega
  rw [Finset.card_union_of_disjoint
    (Finset.disjoint_union_left.mpr ⟨hd, armExtras_disjoint_transpose M b δ hM⟩)]
  rw [Finset.card_union_of_disjoint (staircase_disjoint_armExtras M b δ (by omega)),
    Finset.card_map, armExtras_card]
  simp only [YoungDiagram.card]
  omega

def candidateLengths (M b δ i : ℕ) : ℕ :=
  if i = 0 then M + b + δ else
  if i = 1 then M - 1 + b else
  if i < M - 2 then M - i else
  if i < M - 1 + b then 2 else
  if i < M + b + δ then 1 else 0

lemma candidate_rowLen (M b δ i : ℕ) (hM : 4 ≤ M) :
    (candidate M b δ).rowLen i = candidateLengths M b δ i := by
  have hh (j : ℕ) : j < (candidate M b δ).rowLen i ↔ j < candidateLengths M b δ i := by
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_candidate]
    unfold candidateLengths
    split_ifs <;> omega
  apply le_antisymm
  · by_contra hn
    have := (hh _).mp (Nat.lt_of_not_ge hn)
    omega
  · by_contra hn
    have := (hh _).mpr (Nat.lt_of_not_ge hn)
    omega

lemma candidate_colLen (M b δ i : ℕ) (hM : 4 ≤ M) :
    (candidate M b δ).colLen i = candidateLengths M b δ i := by
  rw [← YoungDiagram.rowLen_transpose, candidate_transpose]
  exact candidate_rowLen M b δ i hM

@[simp] lemma candidate_zero (M : ℕ) : candidate M 0 0 = Saxl.staircase M := by
  apply SetLike.ext
  rintro ⟨i, j⟩
  simp only [mem_candidate, Saxl.mem_staircase]
  omega

def fixedCandidate (n : ℕ) : YoungDiagram :=
  candidate (staircaseIndex n) (remainderPairs n / 2) (remainderPairs n % 2)

@[simp] lemma fixedCandidate_transpose (n : ℕ) :
    (fixedCandidate n).transpose = fixedCandidate n := candidate_transpose _ _ _

lemma fixedCandidate_eq_staircase_of_remainder_zero (n : ℕ)
    (hr : remainderPairs n = 0) :
    fixedCandidate n = Saxl.staircase (staircaseIndex n) := by
  simp only [fixedCandidate, hr, Nat.zero_div, Nat.zero_mod, candidate_zero]

lemma fixedCandidate_card (n : ℕ) (hM : 3 ≤ staircaseIndex n) :
    (fixedCandidate n).card = n := by
  rw [fixedCandidate, candidate_card _ _ _ hM]
  have hd := degree_eq n
  omega

theorem fixedCandidate_large_degree (n : ℕ) (hn : 64 < n) :
    9 ≤ staircaseIndex n ∧ (fixedCandidate n).card = n ∧
      (fixedCandidate n).transpose = fixedCandidate n := by
  have hM : 9 ≤ staircaseIndex n := by
    by_contra h
    exact (not_le_of_gt hn) (degree_le_64_of_small_index n (by omega))
  exact ⟨hM, fixedCandidate_card n (by omega), fixedCandidate_transpose n⟩

end UniversalTensorSquare
end
end

end OAI
