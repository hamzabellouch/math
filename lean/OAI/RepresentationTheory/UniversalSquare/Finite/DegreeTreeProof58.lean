import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData58
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes78

namespace OAI

/-! Degree Tree Proof 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree58_0All : degreeTree58_0.All (RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31964,⟨sg31957,⟨sg31954,⟨sg31952,⟨sg31951,True.intro,True.intro⟩,⟨sg31953,True.intro,True.intro⟩⟩,⟨sg31956,⟨sg31955,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg31961,⟨sg31959,⟨sg31958,True.intro,True.intro⟩,⟨sg31960,True.intro,True.intro⟩⟩,⟨sg31963,⟨sg31962,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg31971,⟨sg31968,⟨sg31966,⟨sg31965,True.intro,True.intro⟩,⟨sg31967,True.intro,True.intro⟩⟩,⟨sg31970,⟨sg31969,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg31975,⟨sg31973,⟨sg31972,True.intro,True.intro⟩,⟨sg31974,True.intro,True.intro⟩⟩,⟨sg31977,⟨sg31976,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree58_1All : degreeTree58_1.All (RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31992,⟨sg31985,⟨sg31982,⟨sg31980,⟨sg31979,True.intro,True.intro⟩,⟨sg31981,True.intro,True.intro⟩⟩,⟨sg31984,⟨sg31983,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg31989,⟨sg31987,⟨sg31986,True.intro,True.intro⟩,⟨sg31988,True.intro,True.intro⟩⟩,⟨sg31991,⟨sg31990,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg31999,⟨sg31996,⟨sg31994,⟨sg31993,True.intro,True.intro⟩,⟨sg31995,True.intro,True.intro⟩⟩,⟨sg31998,⟨sg31997,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32003,⟨sg32001,⟨sg32000,True.intro,True.intro⟩,⟨sg32002,True.intro,True.intro⟩⟩,⟨sg32005,⟨sg32004,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree58_2All : degreeTree58_2.All (RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31978,degreeTree58_0All,degreeTree58_1All⟩

lemma degreeTreeAll58 : degreeTree58.All
    (fun rs => SquareOccurs (candidate 8 5 1) (rowDiagram rs)) := by
  have hp : rowDiagram [14,12,6,5,4,3,2,2,2,2,2,2,1,1] = candidate 8 5 1 := rowDiagram_candidate (M := 8) (b := 5) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree58_2All

end UniversalTensorSquare
end
end

end OAI
