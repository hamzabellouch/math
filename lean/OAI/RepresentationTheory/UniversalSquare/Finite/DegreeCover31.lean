import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans31
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData31

namespace OAI

/-! Degree Cover 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover31_0_0 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 1 1 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_0_1 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 1 2 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_0_2 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 1 3 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_0_3 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 1 4 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_0_4 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 1 5 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_1_0 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 2 1 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_1_1 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 2 2 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_1_2 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 2 3 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_1_3 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 2 4 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_1_4 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 2 5 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_2_0 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 3 1 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_2_1 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 3 2 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_2_2 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 3 3 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_2_3 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 3 4 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_2_4 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 3 5 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_3_0 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 4 1 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_3_1 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 4 2 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_3_2 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 4 3 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_3_3 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 4 4 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_3_4 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 4 5 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_4_0 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 5 1 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_4_1 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 5 2 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_4_2 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 5 3 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_4_3 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 5 4 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31_4_4 :
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 5 5 (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  decide +kernel

lemma degreeCover31 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      regionCheck 31 6 5 (d+1) (e+1) (a+1) (c+1) degreeRows31_0 degreeRegions31 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover31_0_0
  · exact degreeCover31_0_1
  · exact degreeCover31_0_2
  · exact degreeCover31_0_3
  · exact degreeCover31_0_4
  · exact degreeCover31_1_0
  · exact degreeCover31_1_1
  · exact degreeCover31_1_2
  · exact degreeCover31_1_3
  · exact degreeCover31_1_4
  · exact degreeCover31_2_0
  · exact degreeCover31_2_1
  · exact degreeCover31_2_2
  · exact degreeCover31_2_3
  · exact degreeCover31_2_4
  · exact degreeCover31_3_0
  · exact degreeCover31_3_1
  · exact degreeCover31_3_2
  · exact degreeCover31_3_3
  · exact degreeCover31_3_4
  · exact degreeCover31_4_0
  · exact degreeCover31_4_1
  · exact degreeCover31_4_2
  · exact degreeCover31_4_3
  · exact degreeCover31_4_4

end UniversalTensorSquare
end
end

end OAI
