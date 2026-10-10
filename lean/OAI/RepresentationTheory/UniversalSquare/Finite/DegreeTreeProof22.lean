import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData22
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes25
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes26

namespace OAI

/-! Degree Tree Proof 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree22_0All : degreeTree22_0.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10919,⟨sg10915,⟨sg10913,⟨sg10912,⟨sg10911,True.intro,True.intro⟩,True.intro⟩,⟨sg10914,True.intro,True.intro⟩⟩,⟨sg10917,⟨sg10916,True.intro,True.intro⟩,⟨sg10918,True.intro,True.intro⟩⟩⟩,⟨sg10924,⟨sg10922,⟨sg10921,⟨sg10920,True.intro,True.intro⟩,True.intro⟩,⟨sg10923,True.intro,True.intro⟩⟩,⟨sg10926,⟨sg10925,True.intro,True.intro⟩,⟨sg10927,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree22_1All : degreeTree22_1.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10937,⟨sg10933,⟨sg10931,⟨sg10930,⟨sg10929,True.intro,True.intro⟩,True.intro⟩,⟨sg10932,True.intro,True.intro⟩⟩,⟨sg10935,⟨sg10934,True.intro,True.intro⟩,⟨sg10936,True.intro,True.intro⟩⟩⟩,⟨sg10941,⟨sg10939,⟨sg10938,True.intro,True.intro⟩,⟨sg10940,True.intro,True.intro⟩⟩,⟨sg10943,⟨sg10942,True.intro,True.intro⟩,⟨sg10944,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree22_2All : degreeTree22_2.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10928,degreeTree22_0All,degreeTree22_1All⟩

lemma degreeTree22_3All : degreeTree22_3.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10954,⟨sg10950,⟨sg10948,⟨sg10947,⟨sg10946,True.intro,True.intro⟩,True.intro⟩,⟨sg10949,True.intro,True.intro⟩⟩,⟨sg10952,⟨sg10951,True.intro,True.intro⟩,⟨sg10953,True.intro,True.intro⟩⟩⟩,⟨sg10958,⟨sg10956,⟨sg10955,True.intro,True.intro⟩,⟨sg10957,True.intro,True.intro⟩⟩,⟨sg10960,⟨sg10959,True.intro,True.intro⟩,⟨sg10961,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree22_4All : degreeTree22_4.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10971,⟨sg10967,⟨sg10965,⟨sg10964,⟨sg10963,True.intro,True.intro⟩,True.intro⟩,⟨sg10966,True.intro,True.intro⟩⟩,⟨sg10969,⟨sg10968,True.intro,True.intro⟩,⟨sg10970,True.intro,True.intro⟩⟩⟩,⟨sg10975,⟨sg10973,⟨sg10972,True.intro,True.intro⟩,⟨sg10974,True.intro,True.intro⟩⟩,⟨sg10977,⟨sg10976,True.intro,True.intro⟩,⟨sg10978,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree22_5All : degreeTree22_5.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10962,degreeTree22_3All,degreeTree22_4All⟩

lemma degreeTree22_6All : degreeTree22_6.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10945,degreeTree22_2All,degreeTree22_5All⟩

lemma degreeTree22_7All : degreeTree22_7.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10988,⟨sg10984,⟨sg10982,⟨sg10981,⟨sg10980,True.intro,True.intro⟩,True.intro⟩,⟨sg10983,True.intro,True.intro⟩⟩,⟨sg10986,⟨sg10985,True.intro,True.intro⟩,⟨sg10987,True.intro,True.intro⟩⟩⟩,⟨sg10993,⟨sg10991,⟨sg10990,⟨sg10989,True.intro,True.intro⟩,True.intro⟩,⟨sg10992,True.intro,True.intro⟩⟩,⟨sg10995,⟨sg10994,True.intro,True.intro⟩,⟨sg10996,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree22_8All : degreeTree22_8.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg11006,⟨sg11002,⟨sg11000,⟨sg10999,⟨sg10998,True.intro,True.intro⟩,True.intro⟩,⟨sg11001,True.intro,True.intro⟩⟩,⟨sg11004,⟨sg11003,True.intro,True.intro⟩,⟨sg11005,True.intro,True.intro⟩⟩⟩,⟨sg11010,⟨sg11008,⟨sg11007,True.intro,True.intro⟩,⟨sg11009,True.intro,True.intro⟩⟩,⟨sg11012,⟨sg11011,True.intro,True.intro⟩,⟨sg11013,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree22_9All : degreeTree22_9.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10997,degreeTree22_7All,degreeTree22_8All⟩

lemma degreeTree22_10All : degreeTree22_10.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg11023,⟨sg11019,⟨sg11017,⟨sg11016,⟨sg11015,True.intro,True.intro⟩,True.intro⟩,⟨sg11018,True.intro,True.intro⟩⟩,⟨sg11021,⟨sg11020,True.intro,True.intro⟩,⟨sg11022,True.intro,True.intro⟩⟩⟩,⟨sg11027,⟨sg11025,⟨sg11024,True.intro,True.intro⟩,⟨sg11026,True.intro,True.intro⟩⟩,⟨sg11029,⟨sg11028,True.intro,True.intro⟩,⟨sg11030,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree22_11All : degreeTree22_11.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg11040,⟨sg11036,⟨sg11034,⟨sg11033,⟨sg11032,True.intro,True.intro⟩,True.intro⟩,⟨sg11035,True.intro,True.intro⟩⟩,⟨sg11038,⟨sg11037,True.intro,True.intro⟩,⟨sg11039,True.intro,True.intro⟩⟩⟩,⟨sg11044,⟨sg11042,⟨sg11041,True.intro,True.intro⟩,⟨sg11043,True.intro,True.intro⟩⟩,⟨sg11046,⟨sg11045,True.intro,True.intro⟩,⟨sg11047,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree22_12All : degreeTree22_12.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg11031,degreeTree22_10All,degreeTree22_11All⟩

lemma degreeTree22_13All : degreeTree22_13.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg11014,degreeTree22_9All,degreeTree22_12All⟩

lemma degreeTree22_14All : degreeTree22_14.All (RowSquare [7,6,2,2,2,2,1]) := by
  exact ⟨sg10979,degreeTree22_6All,degreeTree22_13All⟩

lemma degreeTreeAll22 : degreeTree22.All
    (fun rs => SquareOccurs (candidate 4 3 0) (rowDiagram rs)) := by
  have hp : rowDiagram [7,6,2,2,2,2,1] = candidate 4 3 0 := rowDiagram_candidate (M := 4) (b := 3) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree22_14All

end UniversalTensorSquare
end
end

end OAI
