import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans41
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData41

namespace OAI

/-! Degree Cover 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover41_0_0 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 1 1 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_0_1 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 1 2 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_0_2 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 1 3 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_0_3 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 1 4 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_0_4 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 1 5 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_1_0 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 2 1 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_1_1 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 2 2 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_1_2 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 2 3 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_1_3 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 2 4 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_1_4 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 2 5 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_2_0 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 3 1 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_2_1 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 3 2 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_2_2 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 3 3 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_2_3 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 3 4 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_2_4 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 3 5 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_3_0 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 4 1 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_3_1 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 4 2 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_3_2 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 4 3 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_3_3 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 4 4 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_3_4 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 4 5 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_4_0 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 5 1 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_4_1 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 5 2 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_4_2 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 5 3 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_4_3 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 5 4 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41_4_4 :
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 5 5 (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  decide +kernel

lemma degreeCover41 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      regionCheck 41 6 10 (d+1) (e+1) (a+1) (c+1) degreeRows41_0 degreeRegions41 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover41_0_0
  · exact degreeCover41_0_1
  · exact degreeCover41_0_2
  · exact degreeCover41_0_3
  · exact degreeCover41_0_4
  · exact degreeCover41_1_0
  · exact degreeCover41_1_1
  · exact degreeCover41_1_2
  · exact degreeCover41_1_3
  · exact degreeCover41_1_4
  · exact degreeCover41_2_0
  · exact degreeCover41_2_1
  · exact degreeCover41_2_2
  · exact degreeCover41_2_3
  · exact degreeCover41_2_4
  · exact degreeCover41_3_0
  · exact degreeCover41_3_1
  · exact degreeCover41_3_2
  · exact degreeCover41_3_3
  · exact degreeCover41_3_4
  · exact degreeCover41_4_0
  · exact degreeCover41_4_1
  · exact degreeCover41_4_2
  · exact degreeCover41_4_3
  · exact degreeCover41_4_4

end UniversalTensorSquare
end
end

end OAI
