import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans62
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData62

namespace OAI

/-! Degree Cover 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover62_0_0 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 1 1 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_0_1 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 1 2 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_0_2 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 1 3 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_0_3 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 1 4 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_0_4 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 1 5 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_1_0 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 2 1 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_1_1 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 2 2 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_1_2 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 2 3 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_1_3 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 2 4 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_1_4 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 2 5 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_2_0 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 3 1 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_2_1 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 3 2 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_2_2 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 3 3 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_2_3 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 3 4 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_2_4 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 3 5 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_3_0 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 4 1 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_3_1 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 4 2 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_3_2 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 4 3 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_3_3 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 4 4 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_3_4 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 4 5 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_4_0 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 5 1 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_4_1 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 5 2 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_4_2 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 5 3 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_4_3 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 5 4 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62_4_4 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 5 5 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

lemma degreeCover62 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 (d+1) (e+1) (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover62_0_0
  · exact degreeCover62_0_1
  · exact degreeCover62_0_2
  · exact degreeCover62_0_3
  · exact degreeCover62_0_4
  · exact degreeCover62_1_0
  · exact degreeCover62_1_1
  · exact degreeCover62_1_2
  · exact degreeCover62_1_3
  · exact degreeCover62_1_4
  · exact degreeCover62_2_0
  · exact degreeCover62_2_1
  · exact degreeCover62_2_2
  · exact degreeCover62_2_3
  · exact degreeCover62_2_4
  · exact degreeCover62_3_0
  · exact degreeCover62_3_1
  · exact degreeCover62_3_2
  · exact degreeCover62_3_3
  · exact degreeCover62_3_4
  · exact degreeCover62_4_0
  · exact degreeCover62_4_1
  · exact degreeCover62_4_2
  · exact degreeCover62_4_3
  · exact degreeCover62_4_4

end UniversalTensorSquare
end
end

end OAI
