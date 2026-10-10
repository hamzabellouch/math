import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard47 : (candidate 9 0 1).card = 47 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan47_0 : PackingPlan := (.join (.twoPaths 8 [5,5,5,5]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.neighbor 2 [2,1,1,1]))))
def degreeRows47_0 : List ℕ := [5,5,5,5,4,3,3,3,3,2,2,2,2,1,1,1]

lemma degreeCone47_0 (μ : YoungDiagram) (hμ : μ.card = 47)
    (hd : RowsDom μ.rowLens degreeRows47_0) : SquareOccurs (candidate 9 0 1) μ := by
  exact candidate_cone (by decide) degreeCard47 degreePlan47_0 degreeRows47_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs47 : List (List ℕ) := []

lemma degreeCones47 : ∀ q ∈ degreeQs47, ∀ μ : YoungDiagram, μ.card = 47 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 9 0 1) μ := by
  intro q hq
  simp only [degreeQs47, List.not_mem_nil] at hq

abbrev degreeP47 := ResidualProperty 9 1 degreeQs47 []

lemma degreeCheck47_0_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_0_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_0_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_0_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_0_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 1 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_1_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 2 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_2_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 3 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_3_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 4 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_0 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 1 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_1 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 2 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_2 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 3 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_3 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 4 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47_4_4 :
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 5 5 (a+1) (c+1) degreeRows47_0 degreeP47 := by
  decide +kernel

lemma degreeCheck47 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows47_0.length, ∀ c ∈ List.range degreeRows47_0.length,
      residualCheck 47 9 1 (d+1) (e+1) (a+1) (c+1) degreeRows47_0 degreeP47 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck47_0_0
  · exact degreeCheck47_0_1
  · exact degreeCheck47_0_2
  · exact degreeCheck47_0_3
  · exact degreeCheck47_0_4
  · exact degreeCheck47_1_0
  · exact degreeCheck47_1_1
  · exact degreeCheck47_1_2
  · exact degreeCheck47_1_3
  · exact degreeCheck47_1_4
  · exact degreeCheck47_2_0
  · exact degreeCheck47_2_1
  · exact degreeCheck47_2_2
  · exact degreeCheck47_2_3
  · exact degreeCheck47_2_4
  · exact degreeCheck47_3_0
  · exact degreeCheck47_3_1
  · exact degreeCheck47_3_2
  · exact degreeCheck47_3_3
  · exact degreeCheck47_3_4
  · exact degreeCheck47_4_0
  · exact degreeCheck47_4_1
  · exact degreeCheck47_4_2
  · exact degreeCheck47_4_3
  · exact degreeCheck47_4_4

lemma degree_pos47 (μ : YoungDiagram) (hμ : μ.card = 47) :
    0 < kronecker (canonicalTableau (candidate 9 0 1) degreeCard47)
      (canonicalTableau (candidate 9 0 1) degreeCard47) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard47 degreeRows47_0 (by decide) (by decide)
    degreePlan47_0 (by decide) (by decide) (by decide) (by decide) degreeP47 ?_
    degreeCheck47 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard47 rfl degreeCones47
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
