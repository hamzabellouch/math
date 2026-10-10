import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData14
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes5

namespace OAI

/-! Degree Tree Proof 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree14_0All : degreeTree14_0.All (RowSquare [5,4,2,2,1]) := by
  exact ⟨sg2613,⟨sg2612,True.intro,True.intro⟩,True.intro⟩

lemma degreeTreeAll14 : degreeTree14.All
    (fun rs => SquareOccurs (candidate 4 1 0) (rowDiagram rs)) := by
  have hp : rowDiagram [5,4,2,2,1] = candidate 4 1 0 := rowDiagram_candidate (M := 4) (b := 1) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree14_0All

end UniversalTensorSquare
end
end

end OAI
