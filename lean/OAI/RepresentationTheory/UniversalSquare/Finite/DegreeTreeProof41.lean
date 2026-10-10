import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData41
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes57

namespace OAI

/-! Degree Tree Proof 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree41_0All : degreeTree41_0.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23542,⟨sg23538,⟨sg23536,⟨sg23535,⟨sg23534,True.intro,True.intro⟩,True.intro⟩,⟨sg23537,True.intro,True.intro⟩⟩,⟨sg23540,⟨sg23539,True.intro,True.intro⟩,⟨sg23541,True.intro,True.intro⟩⟩⟩,⟨sg23547,⟨sg23545,⟨sg23544,⟨sg23543,True.intro,True.intro⟩,True.intro⟩,⟨sg23546,True.intro,True.intro⟩⟩,⟨sg23549,⟨sg23548,True.intro,True.intro⟩,⟨sg23550,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree41_1All : degreeTree41_1.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23560,⟨sg23556,⟨sg23554,⟨sg23553,⟨sg23552,True.intro,True.intro⟩,True.intro⟩,⟨sg23555,True.intro,True.intro⟩⟩,⟨sg23558,⟨sg23557,True.intro,True.intro⟩,⟨sg23559,True.intro,True.intro⟩⟩⟩,⟨sg23564,⟨sg23562,⟨sg23561,True.intro,True.intro⟩,⟨sg23563,True.intro,True.intro⟩⟩,⟨sg23566,⟨sg23565,True.intro,True.intro⟩,⟨sg23567,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree41_2All : degreeTree41_2.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23551,degreeTree41_0All,degreeTree41_1All⟩

lemma degreeTree41_3All : degreeTree41_3.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23577,⟨sg23573,⟨sg23571,⟨sg23570,⟨sg23569,True.intro,True.intro⟩,True.intro⟩,⟨sg23572,True.intro,True.intro⟩⟩,⟨sg23575,⟨sg23574,True.intro,True.intro⟩,⟨sg23576,True.intro,True.intro⟩⟩⟩,⟨sg23582,⟨sg23580,⟨sg23579,⟨sg23578,True.intro,True.intro⟩,True.intro⟩,⟨sg23581,True.intro,True.intro⟩⟩,⟨sg23584,⟨sg23583,True.intro,True.intro⟩,⟨sg23585,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree41_4All : degreeTree41_4.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23595,⟨sg23591,⟨sg23589,⟨sg23588,⟨sg23587,True.intro,True.intro⟩,True.intro⟩,⟨sg23590,True.intro,True.intro⟩⟩,⟨sg23593,⟨sg23592,True.intro,True.intro⟩,⟨sg23594,True.intro,True.intro⟩⟩⟩,⟨sg23599,⟨sg23597,⟨sg23596,True.intro,True.intro⟩,⟨sg23598,True.intro,True.intro⟩⟩,⟨sg23601,⟨sg23600,True.intro,True.intro⟩,⟨sg23602,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree41_5All : degreeTree41_5.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23586,degreeTree41_3All,degreeTree41_4All⟩

lemma degreeTree41_6All : degreeTree41_6.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23568,degreeTree41_2All,degreeTree41_5All⟩

lemma degreeTree41_7All : degreeTree41_7.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23612,⟨sg23608,⟨sg23606,⟨sg23605,⟨sg23604,True.intro,True.intro⟩,True.intro⟩,⟨sg23607,True.intro,True.intro⟩⟩,⟨sg23610,⟨sg23609,True.intro,True.intro⟩,⟨sg23611,True.intro,True.intro⟩⟩⟩,⟨sg23617,⟨sg23615,⟨sg23614,⟨sg23613,True.intro,True.intro⟩,True.intro⟩,⟨sg23616,True.intro,True.intro⟩⟩,⟨sg23619,⟨sg23618,True.intro,True.intro⟩,⟨sg23620,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree41_8All : degreeTree41_8.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23630,⟨sg23626,⟨sg23624,⟨sg23623,⟨sg23622,True.intro,True.intro⟩,True.intro⟩,⟨sg23625,True.intro,True.intro⟩⟩,⟨sg23628,⟨sg23627,True.intro,True.intro⟩,⟨sg23629,True.intro,True.intro⟩⟩⟩,⟨sg23634,⟨sg23632,⟨sg23631,True.intro,True.intro⟩,⟨sg23633,True.intro,True.intro⟩⟩,⟨sg23636,⟨sg23635,True.intro,True.intro⟩,⟨sg23637,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree41_9All : degreeTree41_9.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23621,degreeTree41_7All,degreeTree41_8All⟩

lemma degreeTree41_10All : degreeTree41_10.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23647,⟨sg23643,⟨sg23641,⟨sg23640,⟨sg23639,True.intro,True.intro⟩,True.intro⟩,⟨sg23642,True.intro,True.intro⟩⟩,⟨sg23645,⟨sg23644,True.intro,True.intro⟩,⟨sg23646,True.intro,True.intro⟩⟩⟩,⟨sg23651,⟨sg23649,⟨sg23648,True.intro,True.intro⟩,⟨sg23650,True.intro,True.intro⟩⟩,⟨sg23653,⟨sg23652,True.intro,True.intro⟩,⟨sg23654,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree41_11All : degreeTree41_11.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23664,⟨sg23660,⟨sg23658,⟨sg23657,⟨sg23656,True.intro,True.intro⟩,True.intro⟩,⟨sg23659,True.intro,True.intro⟩⟩,⟨sg23662,⟨sg23661,True.intro,True.intro⟩,⟨sg23663,True.intro,True.intro⟩⟩⟩,⟨sg23668,⟨sg23666,⟨sg23665,True.intro,True.intro⟩,⟨sg23667,True.intro,True.intro⟩⟩,⟨sg23670,⟨sg23669,True.intro,True.intro⟩,⟨sg23671,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree41_12All : degreeTree41_12.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23655,degreeTree41_10All,degreeTree41_11All⟩

lemma degreeTree41_13All : degreeTree41_13.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23638,degreeTree41_9All,degreeTree41_12All⟩

lemma degreeTree41_14All : degreeTree41_14.All (RowSquare [11,10,4,3,2,2,2,2,2,2,1]) := by
  exact ⟨sg23603,degreeTree41_6All,degreeTree41_13All⟩

lemma degreeTreeAll41 : degreeTree41.All
    (fun rs => SquareOccurs (candidate 6 5 0) (rowDiagram rs)) := by
  have hp : rowDiagram [11,10,4,3,2,2,2,2,2,2,1] = candidate 6 5 0 := rowDiagram_candidate (M := 6) (b := 5) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree41_14All

end UniversalTensorSquare
end
end

end OAI
