import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData19
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes14

namespace OAI

/-! Degree Tree Proof 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree19_0All : degreeTree19_0.All (RowSquare [6,5,3,2,2,1]) := by
  exact ⟨sg6462,⟨sg6461,True.intro,True.intro⟩,⟨sg6463,True.intro,True.intro⟩⟩

lemma degreeTreeAll19 : degreeTree19.All
    (fun rs => SquareOccurs (candidate 5 1 0) (rowDiagram rs)) := by
  have hp : rowDiagram [6,5,3,2,2,1] = candidate 5 1 0 := rowDiagram_candidate (M := 5) (b := 1) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree19_0All

end UniversalTensorSquare
end
end

end OAI
