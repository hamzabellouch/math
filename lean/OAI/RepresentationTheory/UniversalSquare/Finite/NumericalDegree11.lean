import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts11_0
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts11_1
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts11_2
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts11_3
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts11_4
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts11_5
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts11_6
import OAI.RepresentationTheory.UniversalSquare.Support.FiniteRowSquares

namespace OAI

/-! Numerical Degree 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def smallKeys11 : List (List ℕ) := [[11],[6,1,1,1,1,1],[5,3,1,1,1],[6,2,1,1,1],[7,1,1,1,1],[5,2,2,2],[4,3,3,1],[4,4,2,1],[5,3,2,1],[6,2,2,1],[5,4,1,1],[6,3,1,1],[7,2,1,1],[8,1,1,1],[4,4,3],[5,3,3],[5,4,2],[6,3,2],[7,2,2],[5,5,1],[6,4,1],[7,3,1],[8,2,1],[9,1,1],[6,5],[7,4],[8,3],[9,2],[10,1]]
lemma smallCover11 : ∀ rs ∈ rowsWithin 11 [] [],
    rs ∈ smallKeys11 ∨ transposeRows rs ∈ smallKeys11 := by
  decide +kernel
lemma smallSupports11 : ∀ q ∈ smallKeys11, RowSquare [4,3,3,1] q := by
  intro q hq
  simp only [smallKeys11, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowSquare_trivial _ (by decide)
  · exact smallSupport11_0
  · exact smallSupport11_1
  · exact smallSupport11_2
  · exact smallSupport11_3
  · exact smallSupport11_4
  · exact smallSupport11_5
  · exact smallSupport11_6
  · exact smallSupport11_7
  · exact smallSupport11_8
  · exact smallSupport11_9
  · exact smallSupport11_10
  · exact smallSupport11_11
  · exact smallSupport11_12
  · exact smallSupport11_13
  · exact smallSupport11_14
  · exact smallSupport11_15
  · exact smallSupport11_16
  · exact smallSupport11_17
  · exact smallSupport11_18
  · exact smallSupport11_19
  · exact smallSupport11_20
  · exact smallSupport11_21
  · exact smallSupport11_22
  · exact smallSupport11_23
  · exact smallSupport11_24
  · exact smallSupport11_25
  · exact smallSupport11_26
  · exact smallSupport11_27

lemma degreeCard11 : (rowDiagram [4,3,3,1]).card = 11 := rowDiagram_card _

lemma degree_pos11 (μ : YoungDiagram) (hμ : μ.card = 11) :
    0 < kronecker (canonicalTableau (rowDiagram [4,3,3,1]) degreeCard11)
      (canonicalTableau (rowDiagram [4,3,3,1]) degreeCard11) (canonicalTableau μ hμ) := by
  exact (rowSquare_of_exhaustion (by decide) (by decide) (by decide)
    smallKeys11 smallSupports11 smallCover11 μ hμ).pos _ _

end UniversalTensorSquare
end
end

end OAI
