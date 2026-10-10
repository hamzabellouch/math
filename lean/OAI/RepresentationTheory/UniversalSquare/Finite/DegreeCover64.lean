import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans64
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData64

namespace OAI

/-! Degree Cover 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover64_0_0 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 1 1 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_0_1 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 1 2 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_0_2 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 1 3 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_0_3 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 1 4 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_0_4 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 1 5 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_1_0 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 2 1 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_1_1 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 2 2 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_1_2 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 2 3 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_1_3 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 2 4 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_1_4 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 2 5 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_2_0 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 3 1 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_2_1 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 3 2 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_2_2 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 3 3 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_2_3 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 3 4 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_2_4 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 3 5 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_3_0 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 4 1 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_3_1 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 4 2 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_3_2 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 4 3 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_3_3 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 4 4 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_3_4 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 4 5 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_4_0 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 5 1 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_4_1 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 5 2 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_4_2 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 5 3 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_4_3 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 5 4 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64_4_4 :
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 5 5 (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  decide +kernel

lemma degreeCover64 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      regionCheck 64 8 14 (d+1) (e+1) (a+1) (c+1) degreeRows64_0 degreeRegions64 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover64_0_0
  · exact degreeCover64_0_1
  · exact degreeCover64_0_2
  · exact degreeCover64_0_3
  · exact degreeCover64_0_4
  · exact degreeCover64_1_0
  · exact degreeCover64_1_1
  · exact degreeCover64_1_2
  · exact degreeCover64_1_3
  · exact degreeCover64_1_4
  · exact degreeCover64_2_0
  · exact degreeCover64_2_1
  · exact degreeCover64_2_2
  · exact degreeCover64_2_3
  · exact degreeCover64_2_4
  · exact degreeCover64_3_0
  · exact degreeCover64_3_1
  · exact degreeCover64_3_2
  · exact degreeCover64_3_3
  · exact degreeCover64_3_4
  · exact degreeCover64_4_0
  · exact degreeCover64_4_1
  · exact degreeCover64_4_2
  · exact degreeCover64_4_3
  · exact degreeCover64_4_4

end UniversalTensorSquare
end
end

end OAI
