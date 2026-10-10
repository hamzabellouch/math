import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard56 : (candidate 8 5 0).card = 56 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan56_0 : PackingPlan := (.join (.neighbor 12 [7,6,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 6 1 [7,6]))))
def degreeRows56_0 : List ℕ := [7,7,6,6,6,6,3,3,3,2,2,2,2,1]

lemma degreeCone56_0 (μ : YoungDiagram) (hμ : μ.card = 56)
    (hd : RowsDom μ.rowLens degreeRows56_0) : SquareOccurs (candidate 8 5 0) μ := by
  exact candidate_cone (by decide) degreeCard56 degreePlan56_0 degreeRows56_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs56 : List (List ℕ) := []

lemma degreeCones56 : ∀ q ∈ degreeQs56, ∀ μ : YoungDiagram, μ.card = 56 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 5 0) μ := by
  intro q hq
  simp only [degreeQs56,List.not_mem_nil] at hq

abbrev degreeP56 := ResidualProperty 8 10 degreeQs56 []

lemma degreeCheck56_0_0 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 1 1 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_0_1 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 1 2 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_0_2 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 1 3 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_0_3 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 1 4 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_0_4 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 1 5 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_1_0 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 2 1 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_1_1 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 2 2 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_1_2 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 2 3 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_1_3 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 2 4 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_1_4 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 2 5 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_2_0 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 3 1 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_2_1 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 3 2 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_2_2 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 3 3 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_2_3 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 3 4 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_2_4 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 3 5 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_3_0 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 4 1 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_3_1 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 4 2 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_3_2 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 4 3 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_3_3 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 4 4 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_3_4 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 4 5 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_0 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 1 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_1 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 2 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_2 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 3 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_3 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 4 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56_4_4 :
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 5 5 (a+1) (c+1) degreeRows56_0 degreeP56 := by
  decide +kernel

lemma degreeCheck56 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows56_0.length, ∀ c ∈ List.range degreeRows56_0.length,
      residualCheck 56 8 10 (d+1) (e+1) (a+1) (c+1) degreeRows56_0 degreeP56 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck56_0_0
  · exact degreeCheck56_0_1
  · exact degreeCheck56_0_2
  · exact degreeCheck56_0_3
  · exact degreeCheck56_0_4
  · exact degreeCheck56_1_0
  · exact degreeCheck56_1_1
  · exact degreeCheck56_1_2
  · exact degreeCheck56_1_3
  · exact degreeCheck56_1_4
  · exact degreeCheck56_2_0
  · exact degreeCheck56_2_1
  · exact degreeCheck56_2_2
  · exact degreeCheck56_2_3
  · exact degreeCheck56_2_4
  · exact degreeCheck56_3_0
  · exact degreeCheck56_3_1
  · exact degreeCheck56_3_2
  · exact degreeCheck56_3_3
  · exact degreeCheck56_3_4
  · exact degreeCheck56_4_0
  · exact degreeCheck56_4_1
  · exact degreeCheck56_4_2
  · exact degreeCheck56_4_3
  · exact degreeCheck56_4_4

lemma degree_pos56 (μ : YoungDiagram) (hμ : μ.card = 56) :
    0 < kronecker (canonicalTableau (candidate 8 5 0) degreeCard56)
      (canonicalTableau (candidate 8 5 0) degreeCard56) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 10) (by decide) (by decide) rfl (by decide)
    degreeCard56 degreeRows56_0 (by decide) (by decide)
    degreePlan56_0 (by decide) (by decide) (by decide) (by decide) degreeP56 ?_
    degreeCheck56 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard56 rfl degreeCones56
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
