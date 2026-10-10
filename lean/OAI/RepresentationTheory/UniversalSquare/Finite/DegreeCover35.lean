import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans35
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData35

namespace OAI

/-! Degree Cover 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover35_0_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_0_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_0_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_0_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_0_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 1 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_1_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 2 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_2_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 3 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_3_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 4 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_0 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 1 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_1 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 2 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_2 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 3 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_3 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 4 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35_4_4 :
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 5 5 (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  decide +kernel

lemma degreeCover35 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      regionCheck 35 6 7 (d+1) (e+1) (a+1) (c+1) degreeRows35_0 degreeRegions35 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover35_0_0
  · exact degreeCover35_0_1
  · exact degreeCover35_0_2
  · exact degreeCover35_0_3
  · exact degreeCover35_0_4
  · exact degreeCover35_1_0
  · exact degreeCover35_1_1
  · exact degreeCover35_1_2
  · exact degreeCover35_1_3
  · exact degreeCover35_1_4
  · exact degreeCover35_2_0
  · exact degreeCover35_2_1
  · exact degreeCover35_2_2
  · exact degreeCover35_2_3
  · exact degreeCover35_2_4
  · exact degreeCover35_3_0
  · exact degreeCover35_3_1
  · exact degreeCover35_3_2
  · exact degreeCover35_3_3
  · exact degreeCover35_3_4
  · exact degreeCover35_4_0
  · exact degreeCover35_4_1
  · exact degreeCover35_4_2
  · exact degreeCover35_4_3
  · exact degreeCover35_4_4

end UniversalTensorSquare
end
end

end OAI
