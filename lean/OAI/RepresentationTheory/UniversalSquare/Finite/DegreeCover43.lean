import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans43
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData43

namespace OAI

/-! Degree Cover 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover43_0_0 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 1 1 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_0_1 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 1 2 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_0_2 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 1 3 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_0_3 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 1 4 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_0_4 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 1 5 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_1_0 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 2 1 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_1_1 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 2 2 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_1_2 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 2 3 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_1_3 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 2 4 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_1_4 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 2 5 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_2_0 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 3 1 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_2_1 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 3 2 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_2_2 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 3 3 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_2_3 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 3 4 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_2_4 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 3 5 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_3_0 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 4 1 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_3_1 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 4 2 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_3_2 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 4 3 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_3_3 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 4 4 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_3_4 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 4 5 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_4_0 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 5 1 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_4_1 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 5 2 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_4_2 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 5 3 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_4_3 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 5 4 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43_4_4 :
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 5 5 (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  decide +kernel

lemma degreeCover43 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      regionCheck 43 6 11 (d+1) (e+1) (a+1) (c+1) degreeRows43_0 degreeRegions43 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover43_0_0
  · exact degreeCover43_0_1
  · exact degreeCover43_0_2
  · exact degreeCover43_0_3
  · exact degreeCover43_0_4
  · exact degreeCover43_1_0
  · exact degreeCover43_1_1
  · exact degreeCover43_1_2
  · exact degreeCover43_1_3
  · exact degreeCover43_1_4
  · exact degreeCover43_2_0
  · exact degreeCover43_2_1
  · exact degreeCover43_2_2
  · exact degreeCover43_2_3
  · exact degreeCover43_2_4
  · exact degreeCover43_3_0
  · exact degreeCover43_3_1
  · exact degreeCover43_3_2
  · exact degreeCover43_3_3
  · exact degreeCover43_3_4
  · exact degreeCover43_4_0
  · exact degreeCover43_4_1
  · exact degreeCover43_4_2
  · exact degreeCover43_4_3
  · exact degreeCover43_4_4

end UniversalTensorSquare
end
end

end OAI
