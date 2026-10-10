import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData116
import OAI.RepresentationTheory.UniversalSquare.Finite.PieriRows116

namespace OAI

/-! Degree Tree Proof 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree116_0All : degreeTree116_0.All (RowSquare [22,20,10,9,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨pieriSquare116_2,⟨pieriSquare116_1,⟨pieriSquare116_0,True.intro,True.intro⟩,True.intro⟩,⟨pieriSquare116_3,True.intro,True.intro⟩⟩

lemma degreeTreeAll116 : degreeTree116.All
    (fun rs => SquareOccurs (candidate 12 9 1) (rowDiagram rs)) := by
  have hp : rowDiagram [22,20,10,9,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,2,1,1] = candidate 12 9 1 := rowDiagram_candidate (M := 12) (b := 9) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree116_0All

end UniversalTensorSquare
end
end

end OAI
