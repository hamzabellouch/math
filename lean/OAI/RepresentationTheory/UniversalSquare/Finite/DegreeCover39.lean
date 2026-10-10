import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans39
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData39

namespace OAI

/-! Degree Cover 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover39_0_0 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 1 1 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_0_1 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 1 2 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_0_2 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 1 3 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_0_3 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 1 4 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_0_4 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 1 5 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_1_0 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 2 1 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_1_1 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 2 2 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_1_2 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 2 3 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_1_3 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 2 4 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_1_4 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 2 5 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_2_0 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 3 1 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_2_1 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 3 2 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_2_2 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 3 3 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_2_3 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 3 4 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_2_4 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 3 5 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_3_0 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 4 1 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_3_1 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 4 2 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_3_2 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 4 3 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_3_3 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 4 4 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_3_4 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 4 5 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_4_0 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 5 1 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_4_1 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 5 2 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_4_2 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 5 3 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_4_3 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 5 4 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39_4_4 :
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 5 5 (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  decide +kernel

lemma degreeCover39 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      regionCheck 39 6 9 (d+1) (e+1) (a+1) (c+1) degreeRows39_0 degreeRegions39 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover39_0_0
  · exact degreeCover39_0_1
  · exact degreeCover39_0_2
  · exact degreeCover39_0_3
  · exact degreeCover39_0_4
  · exact degreeCover39_1_0
  · exact degreeCover39_1_1
  · exact degreeCover39_1_2
  · exact degreeCover39_1_3
  · exact degreeCover39_1_4
  · exact degreeCover39_2_0
  · exact degreeCover39_2_1
  · exact degreeCover39_2_2
  · exact degreeCover39_2_3
  · exact degreeCover39_2_4
  · exact degreeCover39_3_0
  · exact degreeCover39_3_1
  · exact degreeCover39_3_2
  · exact degreeCover39_3_3
  · exact degreeCover39_3_4
  · exact degreeCover39_4_0
  · exact degreeCover39_4_1
  · exact degreeCover39_4_2
  · exact degreeCover39_4_3
  · exact degreeCover39_4_4

end UniversalTensorSquare
end
end

end OAI
