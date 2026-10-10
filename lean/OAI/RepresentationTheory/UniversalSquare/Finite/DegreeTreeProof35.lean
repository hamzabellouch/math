import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData35
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes52

namespace OAI

/-! Degree Tree Proof 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree35_0All : degreeTree35_0.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21357,⟨sg21353,⟨sg21351,⟨sg21350,⟨sg21349,True.intro,True.intro⟩,True.intro⟩,⟨sg21352,True.intro,True.intro⟩⟩,⟨sg21355,⟨sg21354,True.intro,True.intro⟩,⟨sg21356,True.intro,True.intro⟩⟩⟩,⟨sg21361,⟨sg21359,⟨sg21358,True.intro,True.intro⟩,⟨sg21360,True.intro,True.intro⟩⟩,⟨sg21363,⟨sg21362,True.intro,True.intro⟩,⟨sg21364,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_1All : degreeTree35_1.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21373,⟨sg21369,⟨sg21367,⟨sg21366,True.intro,True.intro⟩,⟨sg21368,True.intro,True.intro⟩⟩,⟨sg21371,⟨sg21370,True.intro,True.intro⟩,⟨sg21372,True.intro,True.intro⟩⟩⟩,⟨sg21377,⟨sg21375,⟨sg21374,True.intro,True.intro⟩,⟨sg21376,True.intro,True.intro⟩⟩,⟨sg21379,⟨sg21378,True.intro,True.intro⟩,⟨sg21380,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_2All : degreeTree35_2.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21365,degreeTree35_0All,degreeTree35_1All⟩

lemma degreeTree35_3All : degreeTree35_3.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21390,⟨sg21386,⟨sg21384,⟨sg21383,⟨sg21382,True.intro,True.intro⟩,True.intro⟩,⟨sg21385,True.intro,True.intro⟩⟩,⟨sg21388,⟨sg21387,True.intro,True.intro⟩,⟨sg21389,True.intro,True.intro⟩⟩⟩,⟨sg21394,⟨sg21392,⟨sg21391,True.intro,True.intro⟩,⟨sg21393,True.intro,True.intro⟩⟩,⟨sg21396,⟨sg21395,True.intro,True.intro⟩,⟨sg21397,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_4All : degreeTree35_4.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21406,⟨sg21402,⟨sg21400,⟨sg21399,True.intro,True.intro⟩,⟨sg21401,True.intro,True.intro⟩⟩,⟨sg21404,⟨sg21403,True.intro,True.intro⟩,⟨sg21405,True.intro,True.intro⟩⟩⟩,⟨sg21410,⟨sg21408,⟨sg21407,True.intro,True.intro⟩,⟨sg21409,True.intro,True.intro⟩⟩,⟨sg21412,⟨sg21411,True.intro,True.intro⟩,⟨sg21413,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_5All : degreeTree35_5.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21398,degreeTree35_3All,degreeTree35_4All⟩

lemma degreeTree35_6All : degreeTree35_6.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21381,degreeTree35_2All,degreeTree35_5All⟩

lemma degreeTree35_7All : degreeTree35_7.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21423,⟨sg21419,⟨sg21417,⟨sg21416,⟨sg21415,True.intro,True.intro⟩,True.intro⟩,⟨sg21418,True.intro,True.intro⟩⟩,⟨sg21421,⟨sg21420,True.intro,True.intro⟩,⟨sg21422,True.intro,True.intro⟩⟩⟩,⟨sg21427,⟨sg21425,⟨sg21424,True.intro,True.intro⟩,⟨sg21426,True.intro,True.intro⟩⟩,⟨sg21429,⟨sg21428,True.intro,True.intro⟩,⟨sg21430,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_8All : degreeTree35_8.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21439,⟨sg21435,⟨sg21433,⟨sg21432,True.intro,True.intro⟩,⟨sg21434,True.intro,True.intro⟩⟩,⟨sg21437,⟨sg21436,True.intro,True.intro⟩,⟨sg21438,True.intro,True.intro⟩⟩⟩,⟨sg21443,⟨sg21441,⟨sg21440,True.intro,True.intro⟩,⟨sg21442,True.intro,True.intro⟩⟩,⟨sg21445,⟨sg21444,True.intro,True.intro⟩,⟨sg21446,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_9All : degreeTree35_9.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21431,degreeTree35_7All,degreeTree35_8All⟩

lemma degreeTree35_10All : degreeTree35_10.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21463,⟨sg21455,⟨sg21451,⟨sg21449,⟨sg21448,True.intro,True.intro⟩,⟨sg21450,True.intro,True.intro⟩⟩,⟨sg21453,⟨sg21452,True.intro,True.intro⟩,⟨sg21454,True.intro,True.intro⟩⟩⟩,⟨sg21459,⟨sg21457,⟨sg21456,True.intro,True.intro⟩,⟨sg21458,True.intro,True.intro⟩⟩,⟨sg21461,⟨sg21460,True.intro,True.intro⟩,⟨sg21462,True.intro,True.intro⟩⟩⟩⟩,⟨sg21471,⟨sg21467,⟨sg21465,⟨sg21464,True.intro,True.intro⟩,⟨sg21466,True.intro,True.intro⟩⟩,⟨sg21469,⟨sg21468,True.intro,True.intro⟩,⟨sg21470,True.intro,True.intro⟩⟩⟩,⟨sg21475,⟨sg21473,⟨sg21472,True.intro,True.intro⟩,⟨sg21474,True.intro,True.intro⟩⟩,⟨sg21477,⟨sg21476,True.intro,True.intro⟩,⟨sg21478,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree35_11All : degreeTree35_11.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21447,degreeTree35_9All,degreeTree35_10All⟩

lemma degreeTree35_12All : degreeTree35_12.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21414,degreeTree35_6All,degreeTree35_11All⟩

lemma degreeTree35_13All : degreeTree35_13.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21488,⟨sg21484,⟨sg21482,⟨sg21481,⟨sg21480,True.intro,True.intro⟩,True.intro⟩,⟨sg21483,True.intro,True.intro⟩⟩,⟨sg21486,⟨sg21485,True.intro,True.intro⟩,⟨sg21487,True.intro,True.intro⟩⟩⟩,⟨sg21492,⟨sg21490,⟨sg21489,True.intro,True.intro⟩,⟨sg21491,True.intro,True.intro⟩⟩,⟨sg21494,⟨sg21493,True.intro,True.intro⟩,⟨sg21495,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_14All : degreeTree35_14.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21504,⟨sg21500,⟨sg21498,⟨sg21497,True.intro,True.intro⟩,⟨sg21499,True.intro,True.intro⟩⟩,⟨sg21502,⟨sg21501,True.intro,True.intro⟩,⟨sg21503,True.intro,True.intro⟩⟩⟩,⟨sg21508,⟨sg21506,⟨sg21505,True.intro,True.intro⟩,⟨sg21507,True.intro,True.intro⟩⟩,⟨sg21510,⟨sg21509,True.intro,True.intro⟩,⟨sg21511,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_15All : degreeTree35_15.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21496,degreeTree35_13All,degreeTree35_14All⟩

lemma degreeTree35_16All : degreeTree35_16.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21528,⟨sg21520,⟨sg21516,⟨sg21514,⟨sg21513,True.intro,True.intro⟩,⟨sg21515,True.intro,True.intro⟩⟩,⟨sg21518,⟨sg21517,True.intro,True.intro⟩,⟨sg21519,True.intro,True.intro⟩⟩⟩,⟨sg21524,⟨sg21522,⟨sg21521,True.intro,True.intro⟩,⟨sg21523,True.intro,True.intro⟩⟩,⟨sg21526,⟨sg21525,True.intro,True.intro⟩,⟨sg21527,True.intro,True.intro⟩⟩⟩⟩,⟨sg21536,⟨sg21532,⟨sg21530,⟨sg21529,True.intro,True.intro⟩,⟨sg21531,True.intro,True.intro⟩⟩,⟨sg21534,⟨sg21533,True.intro,True.intro⟩,⟨sg21535,True.intro,True.intro⟩⟩⟩,⟨sg21540,⟨sg21538,⟨sg21537,True.intro,True.intro⟩,⟨sg21539,True.intro,True.intro⟩⟩,⟨sg21542,⟨sg21541,True.intro,True.intro⟩,⟨sg21543,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree35_17All : degreeTree35_17.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21512,degreeTree35_15All,degreeTree35_16All⟩

lemma degreeTree35_18All : degreeTree35_18.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21553,⟨sg21549,⟨sg21547,⟨sg21546,⟨sg21545,True.intro,True.intro⟩,True.intro⟩,⟨sg21548,True.intro,True.intro⟩⟩,⟨sg21551,⟨sg21550,True.intro,True.intro⟩,⟨sg21552,True.intro,True.intro⟩⟩⟩,⟨sg21557,⟨sg21555,⟨sg21554,True.intro,True.intro⟩,⟨sg21556,True.intro,True.intro⟩⟩,⟨sg21559,⟨sg21558,True.intro,True.intro⟩,⟨sg21560,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_19All : degreeTree35_19.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21569,⟨sg21565,⟨sg21563,⟨sg21562,True.intro,True.intro⟩,⟨sg21564,True.intro,True.intro⟩⟩,⟨sg21567,⟨sg21566,True.intro,True.intro⟩,⟨sg21568,True.intro,True.intro⟩⟩⟩,⟨sg21573,⟨sg21571,⟨sg21570,True.intro,True.intro⟩,⟨sg21572,True.intro,True.intro⟩⟩,⟨sg21575,⟨sg21574,True.intro,True.intro⟩,⟨sg21576,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree35_20All : degreeTree35_20.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21561,degreeTree35_18All,degreeTree35_19All⟩

lemma degreeTree35_21All : degreeTree35_21.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21593,⟨sg21585,⟨sg21581,⟨sg21579,⟨sg21578,True.intro,True.intro⟩,⟨sg21580,True.intro,True.intro⟩⟩,⟨sg21583,⟨sg21582,True.intro,True.intro⟩,⟨sg21584,True.intro,True.intro⟩⟩⟩,⟨sg21589,⟨sg21587,⟨sg21586,True.intro,True.intro⟩,⟨sg21588,True.intro,True.intro⟩⟩,⟨sg21591,⟨sg21590,True.intro,True.intro⟩,⟨sg21592,True.intro,True.intro⟩⟩⟩⟩,⟨sg21601,⟨sg21597,⟨sg21595,⟨sg21594,True.intro,True.intro⟩,⟨sg21596,True.intro,True.intro⟩⟩,⟨sg21599,⟨sg21598,True.intro,True.intro⟩,⟨sg21600,True.intro,True.intro⟩⟩⟩,⟨sg21605,⟨sg21603,⟨sg21602,True.intro,True.intro⟩,⟨sg21604,True.intro,True.intro⟩⟩,⟨sg21607,⟨sg21606,True.intro,True.intro⟩,⟨sg21608,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree35_22All : degreeTree35_22.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21577,degreeTree35_20All,degreeTree35_21All⟩

lemma degreeTree35_23All : degreeTree35_23.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21544,degreeTree35_17All,degreeTree35_22All⟩

lemma degreeTree35_24All : degreeTree35_24.All (RowSquare [10,8,4,3,2,2,2,2,1,1]) := by
  exact ⟨sg21479,degreeTree35_12All,degreeTree35_23All⟩

lemma degreeTreeAll35 : degreeTree35.All
    (fun rs => SquareOccurs (candidate 6 3 1) (rowDiagram rs)) := by
  have hp : rowDiagram [10,8,4,3,2,2,2,2,1,1] = candidate 6 3 1 := rowDiagram_candidate (M := 6) (b := 3) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree35_24All

end UniversalTensorSquare
end
end

end OAI
