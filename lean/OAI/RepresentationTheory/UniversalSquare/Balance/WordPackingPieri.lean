import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPackingGeometry
import OAI.RepresentationTheory.UniversalSquare.Specht.PieriInduction
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPackingPairs

namespace OAI

/-! Word Packing Pieri. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance
open FlagColumns Columns

lemma short_transpose_height (r δ : ℕ) : (ShortColumns.shape r δ).transpose.colLen 0 = r+δ := by
  rw [YoungDiagram.colLen_transpose]
  exact YoungDiagram.rowLen_ofRowLens (hw := by apply List.Pairwise.sortedGE; simp)
    (show Fin [r+δ,r].length from ⟨0,by simp⟩)

lemma repeat_transpose_height {m k : ℕ} (hm : 0 < m) :
    (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose.colLen 0 = k := by
  rw [YoungDiagram.colLen_transpose]
  simpa only [Fin.getElem_fin,List.getElem_replicate] using
    YoungDiagram.rowLen_ofRowLens (hw := replicate_sorted m k)
      (show Fin (List.replicate m k).length from ⟨0,by simpa⟩)

lemma repeat_transpose_rows {m k : ℕ} (hk : 0 < k) :
    (YoungDiagram.ofRowLens (List.replicate m k) (replicate_sorted m k)).transpose.transpose.rowLens =
      List.replicate m k := by
  rw [YoungDiagram.transpose_transpose]
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  rw [(List.mem_replicate.mp hx).2]
  exact hk

lemma repeated_twos_shape (m : ℕ) :
    (YoungDiagram.ofRowLens (List.replicate m 2) (replicate_sorted m 2)).transpose =
      ShortColumns.shape m 0 := by
  apply YoungDiagram.ext
  apply Finset.ext
  intro x
  rcases x with ⟨i,j⟩
  change (i,j) ∈ (YoungDiagram.ofRowLens (List.replicate m 2) (replicate_sorted m 2)).transpose ↔
    (i,j) ∈ ShortColumns.shape m 0
  simp only [YoungDiagram.mem_transpose,YoungDiagram.mem_ofRowLens,
    List.length_replicate,List.getElem_replicate,ShortColumns.mem_shape,Prod.swap_prod_mk]
  simp only [exists_prop,Nat.add_zero]
  omega

lemma two_paths_two_support_sizes {n a b q : ℕ} {ν : YoungDiagram}
    (hn : n = 2*q+4) (ha : a = 2*q+2) (hb : b = 2) (hq : 3 ≤ q)
    (t : Tableau a (ShortColumns.shape q 2).transpose) (u : Tableau b ν)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (hu : ∀ i, (columnLengthWord u i).val+1 = 1) :
    SupportLE (wordRep n 4)
      (Representation.coind (sumPermHom e)
        (outer (projectedSpechtTensor t t (inOutputs (Set.Icc q (2*q+3)))
          (inOutputs_invariant (Set.Icc q (2*q+3)))).toRepresentation
          (projectedSpechtTensor u u (inOutputs {1}) (inOutputs_invariant {1})).toRepresentation)) := by
  subst n a b
  exact (two_paths_two_coind q hq t e).trans
    (SupportLE.coind _ ((SupportLE.refl _).outer (constant_output_support u 1 hu)))

theorem WordPacking.twoPaths {q d : ℕ} (hq : 3 ≤ q) (hd : q+2 ≤ d)
    {ps : List ℕ} (hsum : ps.sum = 2*q+4) (hlen : ps.length ≤ 4)
    (k l : ℕ) (hne : k ≠ l) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a ∈ Set.Icc q (2*q+3))
    (he' : ∀ a, (A a ∧ label a = l) ↔ output a = 1) :
    Nonempty (WordPacking ([q+2,q] ++ List.replicate 2 1) ps d A label {k,l}) := by
  have hrow : (ShortColumns.shape q 2).rowLens = [q+2,q] :=
    YoungDiagram.rowLens_ofRowLens_eq_self (by simp; omega)
  let ν := (YoungDiagram.ofRowLens (List.replicate 2 1) (replicate_sorted 2 1)).transpose
  apply WordPacking.of_binary_shapes (μ := (ShortColumns.shape q 2).transpose) (ν := ν)
    (by rw [YoungDiagram.transpose_transpose,hrow]) (by rw [repeat_transpose_rows (by decide)])
    (by rw [short_transpose_height]; exact hd)
    (by rw [repeat_transpose_height (by decide)]; omega)
    (by simp; omega) hlen k l hne _ {1} A label he he'
  intro t u
  exact two_paths_two_support_sizes (by simp; omega) (by simp; omega) (by simp)
    hq t u (appendPositions _ _) (repeated_column_length (by decide) u)

lemma even_twos_odd_support_sizes {n a b m x : ℕ} {ν : YoungDiagram}
    (hn : n = 2*m+x) (ha : a = 2*m) (hb : b = x)
    (hm : 1 ≤ m) (hx : Odd x) (hxc : x ≤ 2*m)
    (t : Tableau a (ShortColumns.shape m 0)) (u : Tableau b ν)
    (e : Fin n ≃ Fin a ⊕ Fin b) (hu : ∀ i, (columnLengthWord u i).val+1 = x) :
    SupportLE (wordRep n 2)
      (Representation.coind (sumPermHom e)
        (outer (projectedSpechtTensor t t (inOutputs {2}) (inOutputs_invariant {2})).toRepresentation
          (projectedSpechtTensor u u (inOutputs {x}) (inOutputs_invariant {x})).toRepresentation)) := by
  subst n a b
  exact (even_twos_odd_coind m x hm hx hxc t e).trans
    (SupportLE.coind _ ((SupportLE.refl _).outer (constant_output_support u x hu)))

theorem WordPacking.twosOdd {m x d : ℕ} (hm : 1 ≤ m) (hx : Odd x) (hxc : x ≤ 2*m)
    (hd : 2 ≤ d) (hd' : x ≤ d)
    {ps : List ℕ} (hsum : ps.sum = 2*m+x) (hlen : ps.length ≤ 2)
    (k l : ℕ) (hne : k ≠ l) (A : Fin (d*d) → Prop) (label : Fin (d*d) → ℕ)
    (he : ∀ a, (A a ∧ label a = k) ↔ output a = 2)
    (he' : ∀ a, (A a ∧ label a = l) ↔ output a = x) :
    Nonempty (WordPacking (List.replicate m 2 ++ [x]) ps d A label {k,l}) := by
  let ν := (YoungDiagram.ofRowLens (List.replicate 1 x) (replicate_sorted 1 x)).transpose
  have hxpos : 0 < x := hx.pos
  have hp : (List.replicate m 2).Perm (ShortColumns.shape m 0).transpose.rowLens := by
    rw [← repeated_twos_shape,repeat_transpose_rows (by decide)]
  apply WordPacking.of_binary_shapes (μ := ShortColumns.shape m 0) (ν := ν) hp
    (by rw [repeat_transpose_rows hxpos]; rfl)
    ((ShortColumns.height_le m 0).trans hd)
    (by rw [repeat_transpose_height (by decide)]; exact hd')
    (by simp only [List.sum_append,List.sum_replicate,List.sum_singleton,smul_eq_mul]; omega)
    hlen k l hne {2} {x} A label he he'
  intro t u
  exact even_twos_odd_support_sizes (by simp; omega) (by simp; omega) (by simp)
    hm hx hxc t u (appendPositions _ _) (repeated_column_length hxpos u)

end Saxl.Balance
end
end

end OAI
