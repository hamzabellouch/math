import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans24
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData24

namespace OAI

/-! Degree Cover 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover24_0_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_0_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_0_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_0_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_0_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 1 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_1_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 2 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_2_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 3 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_3_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 4 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_0 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 1 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_1 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 2 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_2 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 3 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_3 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 4 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24_4_4 :
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 5 5 (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  decide +kernel

lemma degreeCover24 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      regionCheck 24 4 7 (d+1) (e+1) (a+1) (c+1) degreeRows24_0 degreeRegions24 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover24_0_0
  · exact degreeCover24_0_1
  · exact degreeCover24_0_2
  · exact degreeCover24_0_3
  · exact degreeCover24_0_4
  · exact degreeCover24_1_0
  · exact degreeCover24_1_1
  · exact degreeCover24_1_2
  · exact degreeCover24_1_3
  · exact degreeCover24_1_4
  · exact degreeCover24_2_0
  · exact degreeCover24_2_1
  · exact degreeCover24_2_2
  · exact degreeCover24_2_3
  · exact degreeCover24_2_4
  · exact degreeCover24_3_0
  · exact degreeCover24_3_1
  · exact degreeCover24_3_2
  · exact degreeCover24_3_3
  · exact degreeCover24_3_4
  · exact degreeCover24_4_0
  · exact degreeCover24_4_1
  · exact degreeCover24_4_2
  · exact degreeCover24_4_3
  · exact degreeCover24_4_4

end UniversalTensorSquare
end
end

end OAI
