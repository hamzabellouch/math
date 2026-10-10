import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans19
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData19

namespace OAI

/-! Degree Cover 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover19_0_0 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 1 1 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_0_1 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 1 2 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_0_2 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 1 3 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_0_3 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 1 4 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_0_4 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 1 5 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_1_0 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 2 1 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_1_1 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 2 2 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_1_2 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 2 3 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_1_3 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 2 4 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_1_4 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 2 5 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_2_0 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 3 1 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_2_1 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 3 2 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_2_2 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 3 3 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_2_3 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 3 4 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_2_4 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 3 5 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_3_0 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 4 1 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_3_1 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 4 2 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_3_2 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 4 3 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_3_3 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 4 4 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_3_4 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 4 5 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_4_0 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 5 1 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_4_1 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 5 2 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_4_2 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 5 3 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_4_3 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 5 4 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19_4_4 :
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 5 5 (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  decide +kernel

lemma degreeCover19 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      regionCheck 19 5 2 (d+1) (e+1) (a+1) (c+1) degreeRows19_0 degreeRegions19 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover19_0_0
  · exact degreeCover19_0_1
  · exact degreeCover19_0_2
  · exact degreeCover19_0_3
  · exact degreeCover19_0_4
  · exact degreeCover19_1_0
  · exact degreeCover19_1_1
  · exact degreeCover19_1_2
  · exact degreeCover19_1_3
  · exact degreeCover19_1_4
  · exact degreeCover19_2_0
  · exact degreeCover19_2_1
  · exact degreeCover19_2_2
  · exact degreeCover19_2_3
  · exact degreeCover19_2_4
  · exact degreeCover19_3_0
  · exact degreeCover19_3_1
  · exact degreeCover19_3_2
  · exact degreeCover19_3_3
  · exact degreeCover19_3_4
  · exact degreeCover19_4_0
  · exact degreeCover19_4_1
  · exact degreeCover19_4_2
  · exact degreeCover19_4_3
  · exact degreeCover19_4_4

end UniversalTensorSquare
end
end

end OAI
