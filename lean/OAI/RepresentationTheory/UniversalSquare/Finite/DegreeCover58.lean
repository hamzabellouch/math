import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans58
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData58

namespace OAI

/-! Degree Cover 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover58_0_0 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 1 1 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_0_1 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 1 2 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_0_2 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 1 3 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_0_3 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 1 4 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_0_4 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 1 5 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_1_0 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 2 1 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_1_1 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 2 2 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_1_2 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 2 3 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_1_3 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 2 4 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_1_4 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 2 5 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_2_0 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 3 1 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_2_1 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 3 2 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_2_2 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 3 3 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_2_3 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 3 4 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_2_4 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 3 5 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_3_0 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 4 1 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_3_1 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 4 2 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_3_2 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 4 3 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_3_3 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 4 4 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_3_4 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 4 5 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_4_0 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 5 1 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_4_1 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 5 2 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_4_2 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 5 3 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_4_3 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 5 4 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58_4_4 :
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 5 5 (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  decide +kernel

lemma degreeCover58 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      regionCheck 58 8 11 (d+1) (e+1) (a+1) (c+1) degreeRows58_0 degreeRegions58 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover58_0_0
  · exact degreeCover58_0_1
  · exact degreeCover58_0_2
  · exact degreeCover58_0_3
  · exact degreeCover58_0_4
  · exact degreeCover58_1_0
  · exact degreeCover58_1_1
  · exact degreeCover58_1_2
  · exact degreeCover58_1_3
  · exact degreeCover58_1_4
  · exact degreeCover58_2_0
  · exact degreeCover58_2_1
  · exact degreeCover58_2_2
  · exact degreeCover58_2_3
  · exact degreeCover58_2_4
  · exact degreeCover58_3_0
  · exact degreeCover58_3_1
  · exact degreeCover58_3_2
  · exact degreeCover58_3_3
  · exact degreeCover58_3_4
  · exact degreeCover58_4_0
  · exact degreeCover58_4_1
  · exact degreeCover58_4_2
  · exact degreeCover58_4_3
  · exact degreeCover58_4_4

end UniversalTensorSquare
end
end

end OAI
