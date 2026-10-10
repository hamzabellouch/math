import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans26
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData26

namespace OAI

/-! Degree Cover 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover26_0_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_0_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_0_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_0_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_0_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 (d+1) (e+1) (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover26_0_0
  · exact degreeCover26_0_1
  · exact degreeCover26_0_2
  · exact degreeCover26_0_3
  · exact degreeCover26_0_4
  · exact degreeCover26_1_0
  · exact degreeCover26_1_1
  · exact degreeCover26_1_2
  · exact degreeCover26_1_3
  · exact degreeCover26_1_4
  · exact degreeCover26_2_0
  · exact degreeCover26_2_1
  · exact degreeCover26_2_2
  · exact degreeCover26_2_3
  · exact degreeCover26_2_4
  · exact degreeCover26_3_0
  · exact degreeCover26_3_1
  · exact degreeCover26_3_2
  · exact degreeCover26_3_3
  · exact degreeCover26_3_4
  · exact degreeCover26_4_0
  · exact degreeCover26_4_1
  · exact degreeCover26_4_2
  · exact degreeCover26_4_3
  · exact degreeCover26_4_4

end UniversalTensorSquare
end
end

end OAI
