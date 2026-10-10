import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.NumericBands

namespace OAI

/-! Finite Diagrams. -/

section

namespace UniversalTensorSquare

def partitionLists : ℕ → ℕ → ℕ → Finset (List ℕ)
  | 0, n, _ => if n = 0 then {[]} else ∅
  | k+1, n, b => (if n = 0 then {[]} else ∅) ∪
      (Finset.Icc 1 (min n b)).biUnion fun a =>
        (partitionLists k (n-a) a).image (List.cons a)

lemma mem_partitionLists (k : ℕ) (rs : List ℕ) (n b : ℕ)
    (hsum : rs.sum = n) (hlen : rs.length ≤ k)
    (hpos : ∀ a ∈ rs, 0 < a) (hbound : ∀ a ∈ rs, a ≤ b)
    (hsort : rs.SortedGE) : rs ∈ partitionLists k n b := by
  induction k generalizing rs n b with
  | zero =>
    have hr : rs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst rs
    simp only [List.sum_nil] at hsum
    subst n
    simp [partitionLists]
  | succ k ih =>
    cases rs with
    | nil =>
      simp only [List.sum_nil] at hsum
      subst n
      simp [partitionLists]
    | cons a rs =>
      have ha : 0 < a := hpos a (by simp)
      have han : a ≤ n := by simp only [List.sum_cons] at hsum; omega
      have hab : a ≤ b := hbound a (by simp)
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨a, Finset.mem_Icc.mpr ⟨ha, le_min han hab⟩, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨rs, ih rs (n-a) a ?_ ?_ ?_ ?_ ?_, rfl⟩
      · simp only [List.sum_cons] at hsum
        omega
      · simpa only [List.length_cons, Nat.succ_le_succ_iff] using hlen
      · intro x hx
        exact hpos x (by simp [hx])
      · intro x hx
        exact (List.pairwise_cons.mp hsort.pairwise).1 x hx
      · exact (List.pairwise_cons.mp hsort.pairwise).2.sortedGE

lemma rowLens_mem_partitionLists (μ : YoungDiagram) :
    μ.rowLens ∈ partitionLists μ.card μ.card μ.card := by
  apply mem_partitionLists
  · exact (Saxl.card_eq_sum_rowLens μ).symm
  · rw [Saxl.card_eq_sum_rowLens]
    exact List.length_le_sum_of_one_le _ fun a ha => μ.pos_of_mem_rowLens a ha
  · exact fun a ha => μ.pos_of_mem_rowLens a ha
  · intro a ha
    rw [Saxl.card_eq_sum_rowLens]
    exact List.single_le_sum (fun x _ => Nat.zero_le x) a ha
  · exact μ.rowLens_sorted

def diagramOfCols (rs : List ℕ) (hs : rs.SortedGE) : YoungDiagram :=
  (YoungDiagram.ofRowLens rs hs).transpose

lemma diagramOfCols_cols (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) : (diagramOfCols rs hs).transpose.rowLens = rs := by
  simp only [diagramOfCols, YoungDiagram.transpose_transpose]
  exact YoungDiagram.rowLens_ofRowLens_eq_self hp

lemma diagramOfCols_card (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) : (diagramOfCols rs hs).card = rs.sum := by
  rw [diagramOfCols, Saxl.transpose_card, Saxl.card_eq_sum_rowLens,
    YoungDiagram.rowLens_ofRowLens_eq_self hp]

lemma eq_diagramOfCols (μ : YoungDiagram) (rs : List ℕ) (hs : rs.SortedGE)
    (h : μ.transpose.rowLens = rs) : μ = diagramOfCols rs hs := by
  subst rs
  simp only [diagramOfCols, YoungDiagram.ofRowLens_to_rowLens_eq_self,
    YoungDiagram.transpose_transpose]

end UniversalTensorSquare
end

end OAI
