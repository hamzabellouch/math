import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.FiniteRowSquares
import OAI.RepresentationTheory.UniversalSquare.Finite.ChoiceCertificates13
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_1
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_2
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_3
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_4
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_5
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_6
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_7
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_8
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_9
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_10
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_11
import OAI.RepresentationTheory.UniversalSquare.Finite.SmallContracts13_12

namespace OAI

/-! Numerical Degree 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

def smallKeys13 : List (List ℕ) := [[13],[7,1,1,1,1,1,1],[6,3,1,1,1,1],[7,2,1,1,1,1],[8,1,1,1,1,1],[6,2,2,2,1],[5,3,3,1,1],[5,4,2,1,1],[6,3,2,1,1],[7,2,2,1,1],[5,5,1,1,1],[6,4,1,1,1],[7,3,1,1,1],[8,2,1,1,1],[9,1,1,1,1],[5,3,3,2],[5,4,2,2],[6,3,2,2],[7,2,2,2],[5,4,3,1],[6,3,3,1],[5,5,2,1],[6,4,2,1],[7,3,2,1],[8,2,2,1],[6,5,1,1],[7,4,1,1],[8,3,1,1],[9,2,1,1],[10,1,1,1],[7,3,3],[6,5,2],[7,4,2],[8,3,2],[9,2,2],[6,6,1],[7,5,1],[8,4,1],[9,3,1],[10,2,1],[11,1,1],[10,3],[12,1],[4,4,3,2],[4,4,4,1],[5,4,4],[5,5,3],[6,4,3],[7,6],[8,5],[9,4],[11,2]]
lemma smallCover13 : ∀ rs ∈ rowsWithin 13 [] [],
    rs ∈ smallKeys13 ∨ transposeRows rs ∈ smallKeys13 := by
  decide +kernel
lemma smallSupports13 : ∀ q ∈ smallKeys13, RowSquare [4,4,3,2] q := by
  intro q hq
  simp only [smallKeys13, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rowSquare_trivial _ (by decide)
  · exact smallSupport13_0
  · exact smallSupport13_1
  · exact smallSupport13_2
  · exact smallSupport13_3
  · exact smallSupport13_4
  · exact smallSupport13_5
  · exact smallSupport13_6
  · exact smallSupport13_7
  · exact smallSupport13_8
  · exact smallSupport13_9
  · exact smallSupport13_10
  · exact smallSupport13_11
  · exact smallSupport13_12
  · exact smallSupport13_13
  · exact smallSupport13_14
  · exact smallSupport13_15
  · exact smallSupport13_16
  · exact smallSupport13_17
  · exact smallSupport13_18
  · exact smallSupport13_19
  · exact smallSupport13_20
  · exact smallSupport13_21
  · exact smallSupport13_22
  · exact smallSupport13_23
  · exact smallSupport13_24
  · exact smallSupport13_25
  · exact smallSupport13_26
  · exact smallSupport13_27
  · exact smallSupport13_28
  · exact smallSupport13_29
  · exact smallSupport13_30
  · exact smallSupport13_31
  · exact smallSupport13_32
  · exact smallSupport13_33
  · exact smallSupport13_34
  · exact smallSupport13_35
  · exact smallSupport13_36
  · exact smallSupport13_37
  · exact smallSupport13_38
  · exact smallSupport13_39
  · exact smallSupport13_40
  · exact smallSupport13_41
  · exact smallSupport13_42
  · exact smallSupport13_43
  · exact smallSupport13_44
  · exact smallSupport13_45
  · exact smallSupport13_46
  · exact smallSupport13_47
  · exact smallSupport13_48
  · exact smallSupport13_49
  · exact smallSupport13_50

lemma degreeCard13 : (rowDiagram [4,4,3,2]).card = 13 := rowDiagram_card _

lemma degree_pos13 (μ : YoungDiagram) (hμ : μ.card = 13) :
    0 < kronecker (canonicalTableau (rowDiagram [4,4,3,2]) degreeCard13)
      (canonicalTableau (rowDiagram [4,4,3,2]) degreeCard13) (canonicalTableau μ hμ) := by
  exact (rowSquare_of_exhaustion (by decide) (by decide) (by decide)
    smallKeys13 smallSupports13 smallCover13 μ hμ).pos _ _

end UniversalTensorSquare
end
end

end OAI
