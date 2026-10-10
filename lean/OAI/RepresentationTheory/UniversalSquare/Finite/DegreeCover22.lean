import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans22
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData22

namespace OAI

/-! Degree Cover 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover22_0_0 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 1 1 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_0_1 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 1 2 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_0_2 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 1 3 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_0_3 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 1 4 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_0_4 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 1 5 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_1_0 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 2 1 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_1_1 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 2 2 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_1_2 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 2 3 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_1_3 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 2 4 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_1_4 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 2 5 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_2_0 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 3 1 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_2_1 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 3 2 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_2_2 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 3 3 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_2_3 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 3 4 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_2_4 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 3 5 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_3_0 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 4 1 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_3_1 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 4 2 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_3_2 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 4 3 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_3_3 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 4 4 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_3_4 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 4 5 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_4_0 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 5 1 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_4_1 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 5 2 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_4_2 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 5 3 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_4_3 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 5 4 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22_4_4 :
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 5 5 (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  decide +kernel

lemma degreeCover22 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      regionCheck 22 4 6 (d+1) (e+1) (a+1) (c+1) degreeRows22_0 degreeRegions22 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover22_0_0
  · exact degreeCover22_0_1
  · exact degreeCover22_0_2
  · exact degreeCover22_0_3
  · exact degreeCover22_0_4
  · exact degreeCover22_1_0
  · exact degreeCover22_1_1
  · exact degreeCover22_1_2
  · exact degreeCover22_1_3
  · exact degreeCover22_1_4
  · exact degreeCover22_2_0
  · exact degreeCover22_2_1
  · exact degreeCover22_2_2
  · exact degreeCover22_2_3
  · exact degreeCover22_2_4
  · exact degreeCover22_3_0
  · exact degreeCover22_3_1
  · exact degreeCover22_3_2
  · exact degreeCover22_3_3
  · exact degreeCover22_3_4
  · exact degreeCover22_4_0
  · exact degreeCover22_4_1
  · exact degreeCover22_4_2
  · exact degreeCover22_4_3
  · exact degreeCover22_4_4

end UniversalTensorSquare
end
end

end OAI
