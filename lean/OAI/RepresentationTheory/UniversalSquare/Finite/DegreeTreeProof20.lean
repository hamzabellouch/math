import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData20
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes18

namespace OAI

/-! Degree Tree Proof 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree20_0All : degreeTree20_0.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7869,⟨sg7865,⟨sg7863,⟨sg7862,⟨sg7861,True.intro,True.intro⟩,True.intro⟩,⟨sg7864,True.intro,True.intro⟩⟩,⟨sg7867,⟨sg7866,True.intro,True.intro⟩,⟨sg7868,True.intro,True.intro⟩⟩⟩,⟨sg7873,⟨sg7871,⟨sg7870,True.intro,True.intro⟩,⟨sg7872,True.intro,True.intro⟩⟩,⟨sg7875,⟨sg7874,True.intro,True.intro⟩,⟨sg7876,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree20_1All : degreeTree20_1.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7886,⟨sg7882,⟨sg7880,⟨sg7879,⟨sg7878,True.intro,True.intro⟩,True.intro⟩,⟨sg7881,True.intro,True.intro⟩⟩,⟨sg7884,⟨sg7883,True.intro,True.intro⟩,⟨sg7885,True.intro,True.intro⟩⟩⟩,⟨sg7890,⟨sg7888,⟨sg7887,True.intro,True.intro⟩,⟨sg7889,True.intro,True.intro⟩⟩,⟨sg7892,⟨sg7891,True.intro,True.intro⟩,⟨sg7893,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree20_2All : degreeTree20_2.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7877,degreeTree20_0All,degreeTree20_1All⟩

lemma degreeTree20_3All : degreeTree20_3.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7903,⟨sg7899,⟨sg7897,⟨sg7896,⟨sg7895,True.intro,True.intro⟩,True.intro⟩,⟨sg7898,True.intro,True.intro⟩⟩,⟨sg7901,⟨sg7900,True.intro,True.intro⟩,⟨sg7902,True.intro,True.intro⟩⟩⟩,⟨sg7907,⟨sg7905,⟨sg7904,True.intro,True.intro⟩,⟨sg7906,True.intro,True.intro⟩⟩,⟨sg7909,⟨sg7908,True.intro,True.intro⟩,⟨sg7910,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree20_4All : degreeTree20_4.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7919,⟨sg7915,⟨sg7913,⟨sg7912,True.intro,True.intro⟩,⟨sg7914,True.intro,True.intro⟩⟩,⟨sg7917,⟨sg7916,True.intro,True.intro⟩,⟨sg7918,True.intro,True.intro⟩⟩⟩,⟨sg7923,⟨sg7921,⟨sg7920,True.intro,True.intro⟩,⟨sg7922,True.intro,True.intro⟩⟩,⟨sg7925,⟨sg7924,True.intro,True.intro⟩,⟨sg7926,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree20_5All : degreeTree20_5.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7911,degreeTree20_3All,degreeTree20_4All⟩

lemma degreeTree20_6All : degreeTree20_6.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7894,degreeTree20_2All,degreeTree20_5All⟩

lemma degreeTree20_7All : degreeTree20_7.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7936,⟨sg7932,⟨sg7930,⟨sg7929,⟨sg7928,True.intro,True.intro⟩,True.intro⟩,⟨sg7931,True.intro,True.intro⟩⟩,⟨sg7934,⟨sg7933,True.intro,True.intro⟩,⟨sg7935,True.intro,True.intro⟩⟩⟩,⟨sg7940,⟨sg7938,⟨sg7937,True.intro,True.intro⟩,⟨sg7939,True.intro,True.intro⟩⟩,⟨sg7942,⟨sg7941,True.intro,True.intro⟩,⟨sg7943,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree20_8All : degreeTree20_8.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7952,⟨sg7948,⟨sg7946,⟨sg7945,True.intro,True.intro⟩,⟨sg7947,True.intro,True.intro⟩⟩,⟨sg7950,⟨sg7949,True.intro,True.intro⟩,⟨sg7951,True.intro,True.intro⟩⟩⟩,⟨sg7956,⟨sg7954,⟨sg7953,True.intro,True.intro⟩,⟨sg7955,True.intro,True.intro⟩⟩,⟨sg7958,⟨sg7957,True.intro,True.intro⟩,⟨sg7959,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree20_9All : degreeTree20_9.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7944,degreeTree20_7All,degreeTree20_8All⟩

lemma degreeTree20_10All : degreeTree20_10.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7969,⟨sg7965,⟨sg7963,⟨sg7962,⟨sg7961,True.intro,True.intro⟩,True.intro⟩,⟨sg7964,True.intro,True.intro⟩⟩,⟨sg7967,⟨sg7966,True.intro,True.intro⟩,⟨sg7968,True.intro,True.intro⟩⟩⟩,⟨sg7973,⟨sg7971,⟨sg7970,True.intro,True.intro⟩,⟨sg7972,True.intro,True.intro⟩⟩,⟨sg7975,⟨sg7974,True.intro,True.intro⟩,⟨sg7976,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree20_11All : degreeTree20_11.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7985,⟨sg7981,⟨sg7979,⟨sg7978,True.intro,True.intro⟩,⟨sg7980,True.intro,True.intro⟩⟩,⟨sg7983,⟨sg7982,True.intro,True.intro⟩,⟨sg7984,True.intro,True.intro⟩⟩⟩,⟨sg7989,⟨sg7987,⟨sg7986,True.intro,True.intro⟩,⟨sg7988,True.intro,True.intro⟩⟩,⟨sg7991,⟨sg7990,True.intro,True.intro⟩,⟨sg7992,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree20_12All : degreeTree20_12.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7977,degreeTree20_10All,degreeTree20_11All⟩

lemma degreeTree20_13All : degreeTree20_13.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7960,degreeTree20_9All,degreeTree20_12All⟩

lemma degreeTree20_14All : degreeTree20_14.All (RowSquare [7,5,2,2,2,1,1]) := by
  exact ⟨sg7927,degreeTree20_6All,degreeTree20_13All⟩

lemma degreeTreeAll20 : degreeTree20.All
    (fun rs => SquareOccurs (candidate 4 2 1) (rowDiagram rs)) := by
  have hp : rowDiagram [7,5,2,2,2,1,1] = candidate 4 2 1 := rowDiagram_candidate (M := 4) (b := 2) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree20_14All

end UniversalTensorSquare
end
end

end OAI
