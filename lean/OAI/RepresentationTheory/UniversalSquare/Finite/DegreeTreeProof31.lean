import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData31
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes50

namespace OAI

/-! Degree Tree Proof 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree31_0All : degreeTree31_0.All (RowSquare [9,7,4,3,2,2,2,1,1]) := by
  exact ⟨sg20595,⟨sg20589,⟨sg20586,⟨sg20584,⟨sg20583,True.intro,True.intro⟩,⟨sg20585,True.intro,True.intro⟩⟩,⟨sg20588,⟨sg20587,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg20592,⟨sg20591,⟨sg20590,True.intro,True.intro⟩,True.intro⟩,⟨sg20594,⟨sg20593,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg20601,⟨sg20598,⟨sg20597,⟨sg20596,True.intro,True.intro⟩,True.intro⟩,⟨sg20600,⟨sg20599,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg20604,⟨sg20603,⟨sg20602,True.intro,True.intro⟩,True.intro⟩,⟨sg20606,⟨sg20605,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree31_1All : degreeTree31_1.All (RowSquare [9,7,4,3,2,2,2,1,1]) := by
  exact ⟨sg20619,⟨sg20613,⟨sg20610,⟨sg20609,⟨sg20608,True.intro,True.intro⟩,True.intro⟩,⟨sg20612,⟨sg20611,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg20616,⟨sg20615,⟨sg20614,True.intro,True.intro⟩,True.intro⟩,⟨sg20618,⟨sg20617,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg20625,⟨sg20622,⟨sg20621,⟨sg20620,True.intro,True.intro⟩,True.intro⟩,⟨sg20624,⟨sg20623,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg20628,⟨sg20627,⟨sg20626,True.intro,True.intro⟩,True.intro⟩,⟨sg20630,⟨sg20629,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree31_2All : degreeTree31_2.All (RowSquare [9,7,4,3,2,2,2,1,1]) := by
  exact ⟨sg20607,degreeTree31_0All,degreeTree31_1All⟩

lemma degreeTreeAll31 : degreeTree31.All
    (fun rs => SquareOccurs (candidate 6 2 1) (rowDiagram rs)) := by
  have hp : rowDiagram [9,7,4,3,2,2,2,1,1] = candidate 6 2 1 := rowDiagram_candidate (M := 6) (b := 2) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree31_2All

end UniversalTensorSquare
end
end

end OAI
