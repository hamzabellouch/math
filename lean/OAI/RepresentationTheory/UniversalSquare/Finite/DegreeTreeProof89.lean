import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData89
import OAI.RepresentationTheory.UniversalSquare.Finite.PieriRows89

namespace OAI

/-! Degree Tree Proof 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree89_0All : degreeTree89_0.All (RowSquare [19,17,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨pieriSquare89_0,True.intro,True.intro⟩

lemma degreeTreeAll89 : degreeTree89.All
    (fun rs => SquareOccurs (candidate 10 8 1) (rowDiagram rs)) := by
  have hp : rowDiagram [19,17,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,1,1] = candidate 10 8 1 := rowDiagram_candidate (M := 10) (b := 8) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree89_0All

end UniversalTensorSquare
end
end

end OAI
