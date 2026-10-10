import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans14
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData14

namespace OAI

/-! Degree Cover 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover14_0_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_0_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_0_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_0_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_0_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 1 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_1_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 2 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_2_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 3 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_3_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 4 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_0 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 1 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_1 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 2 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_2 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 3 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_3 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 4 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14_4_4 :
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 5 5 (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  decide +kernel

lemma degreeCover14 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      regionCheck 14 4 2 (d+1) (e+1) (a+1) (c+1) degreeRows14_0 degreeRegions14 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover14_0_0
  · exact degreeCover14_0_1
  · exact degreeCover14_0_2
  · exact degreeCover14_0_3
  · exact degreeCover14_0_4
  · exact degreeCover14_1_0
  · exact degreeCover14_1_1
  · exact degreeCover14_1_2
  · exact degreeCover14_1_3
  · exact degreeCover14_1_4
  · exact degreeCover14_2_0
  · exact degreeCover14_2_1
  · exact degreeCover14_2_2
  · exact degreeCover14_2_3
  · exact degreeCover14_2_4
  · exact degreeCover14_3_0
  · exact degreeCover14_3_1
  · exact degreeCover14_3_2
  · exact degreeCover14_3_3
  · exact degreeCover14_3_4
  · exact degreeCover14_4_0
  · exact degreeCover14_4_1
  · exact degreeCover14_4_2
  · exact degreeCover14_4_3
  · exact degreeCover14_4_4

end UniversalTensorSquare
end
end

end OAI
