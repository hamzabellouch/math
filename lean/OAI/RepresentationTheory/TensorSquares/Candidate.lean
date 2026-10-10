import Mathlib
import OAI.RepresentationTheory.TensorSquares.Arithmetic
import OAI.RepresentationTheory.Saxl.Model

namespace OAI

/-! Self-conjugate Young diagrams with prescribed size. -/

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquares
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

def candidateArm (m r : ℕ) : YoungDiagram :=
  rectangle 1 (m + r / 2 + r % 2) ⊔ rectangle 2 (m - 1 + r / 2)

def candidate (m r : ℕ) : YoungDiagram :=
  Saxl.staircase m ⊔ candidateArm m r ⊔ (candidateArm m r).transpose

lemma mem_candidate {m r i j : ℕ} :
    (i, j) ∈ candidate m r ↔
      (i + j < m ∨
        (i < 1 ∧ j < m + r / 2 + r % 2 ∨ i < 2 ∧ j < m - 1 + r / 2)) ∨
      (j < 1 ∧ i < m + r / 2 + r % 2 ∨ j < 2 ∧ i < m - 1 + r / 2) := by
  simp only [candidate, candidateArm, YoungDiagram.mem_sup, Saxl.mem_staircase,
    YoungDiagram.mem_transpose, Prod.swap_prod_mk, mem_rectangle]

@[simp] lemma candidate_transpose (m r : ℕ) : (candidate m r).transpose = candidate m r := by
  apply SetLike.ext
  rintro ⟨i, j⟩
  simp only [YoungDiagram.mem_transpose, Prod.swap_prod_mk, mem_candidate]
  omega

@[simp] lemma candidate_zero (m : ℕ) : candidate m 0 = Saxl.staircase m := by
  apply SetLike.ext
  rintro ⟨i, j⟩
  simp only [mem_candidate, Saxl.mem_staircase, Nat.zero_div, Nat.zero_mod, Nat.add_zero]
  omega

def rightCells (m r : ℕ) : Finset (ℕ × ℕ) :=
  ({0} ×ˢ Finset.Ico m (m + r / 2 + r % 2)) ∪
    ({1} ×ˢ Finset.Ico (m - 1) (m - 1 + r / 2))

lemma mem_rightCells {m r i j : ℕ} :
    (i, j) ∈ rightCells m r ↔
      (i = 0 ∧ m ≤ j ∧ j < m + r / 2 + r % 2) ∨
      (i = 1 ∧ m - 1 ≤ j ∧ j < m - 1 + r / 2) := by
  simp only [rightCells, Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico]

lemma rightCells_card (m r : ℕ) : (rightCells m r).card = r := by
  have hd : Disjoint
      ({0} ×ˢ Finset.Ico m (m + r / 2 + r % 2))
      ({1} ×ˢ Finset.Ico (m - 1) (m - 1 + r / 2)) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨i, j⟩ hi hj
    simp only [Finset.mem_product, Finset.mem_singleton] at hi hj
    omega
  rw [rightCells, Finset.card_union_of_disjoint hd]
  simp only [Finset.card_product, Finset.card_singleton, one_mul, Nat.card_Ico]
  omega

lemma candidate_cells (m r : ℕ) (hm : 3 ≤ m) :
    (candidate m r).cells =
      ((Saxl.staircase m).cells ∪ rightCells m r) ∪
        (rightCells m r).map (Equiv.prodComm ℕ ℕ).toEmbedding := by
  ext ⟨i, j⟩
  simp only [YoungDiagram.mem_cells, mem_candidate, Finset.mem_union, Saxl.mem_staircase,
    Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
    mem_rightCells]
  omega

lemma candidate_card (m r : ℕ) (hm : 3 ≤ m) :
    (candidate m r).card = triangular m + 2 * r := by
  have hd₁ : Disjoint (Saxl.staircase m).cells (rightCells m r) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨i, j⟩ hi hj
    simp only [YoungDiagram.mem_cells, Saxl.mem_staircase] at hi
    rw [mem_rightCells] at hj
    omega
  have hd₂ : Disjoint ((Saxl.staircase m).cells ∪ rightCells m r)
      ((rightCells m r).map (Equiv.prodComm ℕ ℕ).toEmbedding) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨i, j⟩ hi hj
    simp only [Finset.mem_union, YoungDiagram.mem_cells, Saxl.mem_staircase,
      mem_rightCells] at hi
    simp only [Finset.mem_map_equiv, Equiv.prodComm_symm, Equiv.prodComm_apply,
      Prod.swap_prod_mk, mem_rightCells] at hj
    omega
  change (candidate m r).cells.card = _
  rw [candidate_cells m r hm, Finset.card_union_of_disjoint hd₂,
    Finset.card_union_of_disjoint hd₁, Finset.card_map, rightCells_card]
  change (Saxl.staircase m).card + r + r = _
  rw [← triangular_eq_staircase_card m]
  omega

lemma candidate_rowLen (m r : ℕ) (hm : 4 ≤ m) (i : ℕ) :
    (candidate m r).rowLen i =
      if i = 0 then m + r / 2 + r % 2 else
      if i = 1 then m - 1 + r / 2 else
      if i < m - 2 then m - i else
      if i < m - 1 + r / 2 then 2 else
      if i < m + r / 2 + r % 2 then 1 else 0 := by
  apply eq_of_forall_lt_iff
  intro j
  rw [← YoungDiagram.mem_iff_lt_rowLen, mem_candidate]
  split_ifs <;> omega

lemma candidate_colLen (m r : ℕ) (hm : 4 ≤ m) (i : ℕ) :
    (candidate m r).colLen i =
      if i = 0 then m + r / 2 + r % 2 else
      if i = 1 then m - 1 + r / 2 else
      if i < m - 2 then m - i else
      if i < m - 1 + r / 2 then 2 else
      if i < m + r / 2 + r % 2 then 1 else 0 := by
  rw [← YoungDiagram.rowLen_transpose, candidate_transpose]
  exact candidate_rowLen m r hm i

theorem candidate_size_and_self_conjugacy (n : ℕ) (hn : 9 ≤ largestIndex n) :
    (candidate (largestIndex n) (remainderPairs n)).card = n ∧
      (candidate (largestIndex n) (remainderPairs n)).transpose =
        candidate (largestIndex n) (remainderPairs n) := by
  constructor
  · rw [candidate_card _ _ (by omega), degree_decomposition]
  · exact candidate_transpose _ _

end UniversalTensorSquares

end

end OAI
