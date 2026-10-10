import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.ConstantOutputs
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPackingLeaves

namespace OAI

/-! Word Packing Geometry. -/

section

noncomputable section
namespace Saxl.Balance
open FlagColumns Columns

theorem WordPacking.of_bounded_shape {rs ps : List ℕ} {μ : YoungDiagram} {d E : ℕ}
    (hp : rs.Perm μ.transpose.rowLens) (hd : μ.colLen 0 ≤ d)
    (hsum : ps.sum = rs.sum) (hlen : ps.length ≤ E)
    (k : ℕ) (I : Set ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ I)
    (hs : ∀ t : Tableau rs.sum μ, SupportLE (wordRep rs.sum E)
      (projectedSpechtTensor t t (inOutputs I) (inOutputs_invariant I)).toRepresentation) :
    Nonempty (WordPacking rs ps d A label {k}) := by
  obtain ⟨e,hr,hc⟩ := place_columns μ hp
  exact ⟨WordPacking.bounded e hr hc hd hsum hlen k I A label he (hs _)⟩

theorem WordPacking.neighbor {r d : ℕ} (hr : 0 < r) (hd : r+1 ≤ d)
    {ps : List ℕ} (hsum : ps.sum = 2*r+1) (hlen : ps.length ≤ 4)
    (k : ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ Set.Icc r (r+1)) :
    Nonempty (WordPacking [r+1,r] ps d A label {k}) := by
  have hrow : (ShortColumns.shape r 1).rowLens = [r+1,r] :=
    YoungDiagram.rowLens_ofRowLens_eq_self (by simp; omega)
  have hD : (ShortColumns.shape r 1).transpose.colLen 0 ≤ d := by
    rw [YoungDiagram.colLen_transpose]
    have hh := YoungDiagram.rowLen_ofRowLens (hw := by apply List.Pairwise.sortedGE; simp)
      (show Fin [r+1,r].length from ⟨0,by simp⟩)
    change (ShortColumns.shape r 1).rowLen 0 = r+1 at hh
    rw [hh]
    exact hd
  apply WordPacking.of_bounded_shape (μ := (ShortColumns.shape r 1).transpose)
    (by rw [YoungDiagram.transpose_transpose,hrow]) hD (by simp; omega) hlen k _ A label he
  intro t
  exact neighboring_word_support (by simp; omega) t

lemma replicate_sorted (m k : ℕ) : (List.replicate m k).SortedGE :=
  List.Pairwise.sortedGE (List.pairwise_replicate.mpr (Or.inr le_rfl))

lemma repeated_column_length {m k n : ℕ} (hk : 0 < k)
    (t : Tableau n (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose)
    (i : Fin n) : (columnLengthWord t i).val+1 = k := by
  have hm := YoungDiagram.mem_transpose.mp (t i).property
  obtain ⟨hj,hi⟩ := YoungDiagram.mem_ofRowLens.mp hm
  have he := YoungDiagram.rowLen_ofRowLens (hw := replicate_sorted m k)
    (show Fin (List.replicate m k).length from ⟨(t i).val.2,hj⟩)
  simp only [Fin.getElem_fin, List.getElem_replicate] at he
  change (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose.colLen
    (t i).val.2 - 1 + 1 = k
  rw [YoungDiagram.colLen_transpose,he]
  omega

theorem WordPacking.repeated {m k d : ℕ} (hm : 0 < m) (hk : 0 < k) (hd : k ≤ d)
    (j : ℕ) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = j) ↔ output a = k) :
    Nonempty (WordPacking (List.replicate m k) [m*k] d A label {j}) := by
  let μ := (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose
  have hrow : μ.transpose.rowLens = List.replicate m k := by
    rw [YoungDiagram.transpose_transpose]
    apply YoungDiagram.rowLens_ofRowLens_eq_self
    intro x hx
    rw [(List.mem_replicate.mp hx).2]
    exact hk
  have hD : μ.colLen 0 ≤ d := by
    rw [YoungDiagram.colLen_transpose]
    have hh := YoungDiagram.rowLen_ofRowLens (hw := replicate_sorted m k)
      (show Fin (List.replicate m k).length from ⟨0,by simpa⟩)
    simp only [Fin.getElem_fin, List.getElem_replicate] at hh
    rw [hh]
    exact hd
  apply WordPacking.of_bounded_shape (μ := μ) (E := 1) (by rw [hrow]) hD
    (by simp) (by simp) j {k} A label he
  intro t
  exact constant_output_support t k (repeated_column_length hk t)

end Saxl.Balance
end
end

end OAI
