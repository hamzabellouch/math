import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData118
import OAI.RepresentationTheory.UniversalSquare.Finite.PieriRows118

namespace OAI

/-! Degree Tree Proof 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree118_0All : degreeTree118_0.All (RowSquare [22,21,10,9,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,2,2,1]) := by
  exact ⟨pieriSquare118_1,⟨pieriSquare118_0,True.intro,True.intro⟩,True.intro⟩

lemma degreeTreeAll118 : degreeTree118.All
    (fun rs => SquareOccurs (candidate 12 10 0) (rowDiagram rs)) := by
  have hp : rowDiagram [22,21,10,9,8,7,6,5,4,3,2,2,2,2,2,2,2,2,2,2,2,1] = candidate 12 10 0 := rowDiagram_candidate (M := 12) (b := 10) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree118_0All

end UniversalTensorSquare
end
end

end OAI
