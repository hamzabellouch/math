import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData37
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes52

namespace OAI

/-! Degree Tree Proof 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree37_0All : degreeTree37_0.All (RowSquare [10,9,4,3,2,2,2,2,2,1]) := by
  exact ⟨sg21656,True.intro,True.intro⟩

lemma degreeTreeAll37 : degreeTree37.All
    (fun rs => SquareOccurs (candidate 6 4 0) (rowDiagram rs)) := by
  have hp : rowDiagram [10,9,4,3,2,2,2,2,2,1] = candidate 6 4 0 := rowDiagram_candidate (M := 6) (b := 4) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree37_0All

end UniversalTensorSquare
end
end

end OAI
