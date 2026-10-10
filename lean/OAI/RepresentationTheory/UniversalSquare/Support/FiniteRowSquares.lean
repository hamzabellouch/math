import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.RowSquareTools

namespace OAI

/-! Finite Row Squares. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma rowSquare_of_exhaustion {n : ℕ} {p : List ℕ} (hp : GoodRows p)
    (hs : transposeRows p = p) (hn : 0 < n) (keys : List (List ℕ))
    (hkeys : ∀ q ∈ keys, RowSquare p q)
    (hcover : ∀ rs ∈ rowsWithin n [] [], rs ∈ keys ∨ transposeRows rs ∈ keys)
    (μ : YoungDiagram) (hμ : μ.card = n) : SquareOccurs (rowDiagram p) μ := by
  have hc := rowsWithin_sound hn μ hμ (by simp [RowBounds]) (by simp [RowBounds]) hcover
  rcases hc with hc | hc
  · simpa only [RowSquare,rowDiagram_rowLens] using hkeys _ hc
  · have hh := hkeys _ hc
    rw [RowSquare,rowDiagram_transposeRows ⟨μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩,
      rowDiagram_rowLens] at hh
    have he : (rowDiagram p).transpose = rowDiagram p := by
      rw [← rowDiagram_transposeRows hp, hs]
    simpa only [YoungDiagram.transpose_transpose] using hh.target_transpose he

end UniversalTensorSquare
end
end

end OAI
