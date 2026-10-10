import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans89
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData89

namespace OAI

/-! Degree Cover 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover89_0_0 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 1 1 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_0_1 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 1 2 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_0_2 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 1 3 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_0_3 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 1 4 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_0_4 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 1 5 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_1_0 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 2 1 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_1_1 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 2 2 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_1_2 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 2 3 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_1_3 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 2 4 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_1_4 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 2 5 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_2_0 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 3 1 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_2_1 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 3 2 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_2_2 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 3 3 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_2_3 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 3 4 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_2_4 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 3 5 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_3_0 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 4 1 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_3_1 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 4 2 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_3_2 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 4 3 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_3_3 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 4 4 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_3_4 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 4 5 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_4_0 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 5 1 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_4_1 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 5 2 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_4_2 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 5 3 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_4_3 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 5 4 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89_4_4 :
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 5 5 (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  decide +kernel

lemma degreeCover89 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      regionCheck 89 10 17 (d+1) (e+1) (a+1) (c+1) degreeRows89_0 degreeRegions89 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover89_0_0
  · exact degreeCover89_0_1
  · exact degreeCover89_0_2
  · exact degreeCover89_0_3
  · exact degreeCover89_0_4
  · exact degreeCover89_1_0
  · exact degreeCover89_1_1
  · exact degreeCover89_1_2
  · exact degreeCover89_1_3
  · exact degreeCover89_1_4
  · exact degreeCover89_2_0
  · exact degreeCover89_2_1
  · exact degreeCover89_2_2
  · exact degreeCover89_2_3
  · exact degreeCover89_2_4
  · exact degreeCover89_3_0
  · exact degreeCover89_3_1
  · exact degreeCover89_3_2
  · exact degreeCover89_3_3
  · exact degreeCover89_3_4
  · exact degreeCover89_4_0
  · exact degreeCover89_4_1
  · exact degreeCover89_4_2
  · exact degreeCover89_4_3
  · exact degreeCover89_4_4

end UniversalTensorSquare
end
end

end OAI
