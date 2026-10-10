import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans16
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData16

namespace OAI

/-! Degree Cover 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover16_0_0 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 1 1 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_0_1 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 1 2 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_0_2 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 1 3 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_0_3 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 1 4 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_0_4 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 1 5 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_1_0 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 2 1 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_1_1 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 2 2 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_1_2 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 2 3 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_1_3 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 2 4 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_1_4 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 2 5 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_2_0 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 3 1 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_2_1 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 3 2 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_2_2 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 3 3 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_2_3 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 3 4 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_2_4 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 3 5 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_3_0 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 4 1 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_3_1 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 4 2 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_3_2 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 4 3 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_3_3 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 4 4 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_3_4 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 4 5 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_4_0 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 5 1 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_4_1 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 5 2 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_4_2 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 5 3 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_4_3 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 5 4 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16_4_4 :
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 5 5 (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  decide +kernel

lemma degreeCover16 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      regionCheck 16 4 3 (d+1) (e+1) (a+1) (c+1) degreeRows16_0 degreeRegions16 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover16_0_0
  · exact degreeCover16_0_1
  · exact degreeCover16_0_2
  · exact degreeCover16_0_3
  · exact degreeCover16_0_4
  · exact degreeCover16_1_0
  · exact degreeCover16_1_1
  · exact degreeCover16_1_2
  · exact degreeCover16_1_3
  · exact degreeCover16_1_4
  · exact degreeCover16_2_0
  · exact degreeCover16_2_1
  · exact degreeCover16_2_2
  · exact degreeCover16_2_3
  · exact degreeCover16_2_4
  · exact degreeCover16_3_0
  · exact degreeCover16_3_1
  · exact degreeCover16_3_2
  · exact degreeCover16_3_3
  · exact degreeCover16_3_4
  · exact degreeCover16_4_0
  · exact degreeCover16_4_1
  · exact degreeCover16_4_2
  · exact degreeCover16_4_3
  · exact degreeCover16_4_4

end UniversalTensorSquare
end
end

end OAI
