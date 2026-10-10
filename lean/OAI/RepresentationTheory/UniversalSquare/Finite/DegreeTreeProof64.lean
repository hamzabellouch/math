import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData64
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupMissingLeaves
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes106

namespace OAI

/-! Degree Tree Proof 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree64_0All : degreeTree64_0.All (RowSquare [15,14,6,5,4,3,2,2,2,2,2,2,2,2,1]) := by
  exact ⟨sg43240,⟨sg43236,⟨sg43234,⟨sg43233,True.intro,True.intro⟩,⟨sg43235,True.intro,True.intro⟩⟩,⟨sg43238,⟨sg43237,True.intro,True.intro⟩,⟨sg43239,True.intro,True.intro⟩⟩⟩,⟨sg43244,⟨sg43242,⟨sg43241,True.intro,True.intro⟩,⟨sg43243,True.intro,True.intro⟩⟩,⟨sg43246,⟨sg43245,True.intro,True.intro⟩,⟨sg43247,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTreeAll64 : degreeTree64.All
    (fun rs => SquareOccurs (candidate 8 7 0) (rowDiagram rs)) := by
  have hp : rowDiagram [15,14,6,5,4,3,2,2,2,2,2,2,2,2,1] = candidate 8 7 0 := rowDiagram_candidate (M := 8) (b := 7) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree64_0All

end UniversalTensorSquare
end
end

end OAI
