import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData16
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes8

namespace OAI

/-! Degree Tree Proof 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree16_0All : degreeTree16_0.All (RowSquare [6,4,2,2,1,1]) := by
  exact ⟨sg4098,⟨sg4092,⟨sg4089,⟨sg4087,⟨sg4086,True.intro,True.intro⟩,⟨sg4088,True.intro,True.intro⟩⟩,⟨sg4091,⟨sg4090,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg4095,⟨sg4094,⟨sg4093,True.intro,True.intro⟩,True.intro⟩,⟨sg4097,⟨sg4096,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg4105,⟨sg4101,⟨sg4100,⟨sg4099,True.intro,True.intro⟩,True.intro⟩,⟨sg4104,⟨sg4103,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg4108,⟨sg4107,⟨sg4106,True.intro,True.intro⟩,True.intro⟩,⟨sg4110,⟨sg4109,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTreeAll16 : degreeTree16.All
    (fun rs => SquareOccurs (candidate 4 1 1) (rowDiagram rs)) := by
  have hp : rowDiagram [6,4,2,2,1,1] = candidate 4 1 1 := rowDiagram_candidate (M := 4) (b := 1) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree16_0All

end UniversalTensorSquare
end
end

end OAI
