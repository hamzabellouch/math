import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData18
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes12
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes13

namespace OAI

/-! Degree Tree Proof 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree18_0All : degreeTree18_0.All (RowSquare [6,5,2,2,2,1]) := by
  exact ⟨sg5719,⟨sg5713,⟨sg5710,⟨sg5708,⟨sg5707,True.intro,True.intro⟩,⟨sg5709,True.intro,True.intro⟩⟩,⟨sg5712,⟨sg5711,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg5716,⟨sg5715,⟨sg5714,True.intro,True.intro⟩,True.intro⟩,⟨sg5718,⟨sg5717,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg5725,⟨sg5722,⟨sg5721,⟨sg5720,True.intro,True.intro⟩,True.intro⟩,⟨sg5724,⟨sg5723,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg5728,⟨sg5727,⟨sg5726,True.intro,True.intro⟩,True.intro⟩,⟨sg5730,⟨sg5729,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTreeAll18 : degreeTree18.All
    (fun rs => SquareOccurs (candidate 4 2 0) (rowDiagram rs)) := by
  have hp : rowDiagram [6,5,2,2,2,1] = candidate 4 2 0 := rowDiagram_candidate (M := 4) (b := 2) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree18_0All

end UniversalTensorSquare
end
end

end OAI
