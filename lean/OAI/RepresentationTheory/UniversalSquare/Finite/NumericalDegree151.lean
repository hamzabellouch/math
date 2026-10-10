import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 151. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard151 : (candidate 14 11 1).card = 151 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan151_0 : PackingPlan := (.join (.twoPaths 24 [13,13,13,13]) (.join (.neighbor 11 [6,6,6,5]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 12 3 [14,13])))))))
def degreeRows151_0 : List ℕ := [14,13,13,13,13,13,6,6,6,5,5,5,5,4,4,4,4,4,3,3,3,3,2]

lemma degreeCone151_0 (μ : YoungDiagram) (hμ : μ.card = 151)
    (hd : RowsDom μ.rowLens degreeRows151_0) : SquareOccurs (candidate 14 11 1) μ := by
  exact candidate_cone (by decide) degreeCard151 degreePlan151_0 degreeRows151_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan151_1 : PackingPlan := (.join (.twoPaths 24 [13,13,13,13]) (.join (.neighbor 11 [6,6,6,5]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 12 2)))))))
def degreeRows151_1 : List ℕ := [24,13,13,13,13,6,6,6,5,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

lemma degreeCone151_1 (μ : YoungDiagram) (hμ : μ.card = 151)
    (hd : RowsDom μ.rowLens degreeRows151_1) : SquareOccurs (candidate 14 11 1) μ := by
  exact candidate_cone (by decide) degreeCard151 degreePlan151_1 degreeRows151_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs151 : List (List ℕ) := [degreeRows151_1]

lemma degreeCones151 : ∀ q ∈ degreeQs151, ∀ μ : YoungDiagram, μ.card = 151 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 14 11 1) μ := by
  intro q hq
  simp only [degreeQs151,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone151_1

abbrev degreeP151 := ResidualProperty 14 23 degreeQs151 []

lemma degreeCheck151_0_0 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 1 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_0_1 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 2 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_0_2 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 3 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_0_3 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 4 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_0_4 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 1 5 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_0 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 1 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_1 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 2 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_2 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 3 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_3 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 4 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_1_4 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 2 5 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_2_0 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 3 1 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_2_1 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 3 2 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_2_2 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 3 3 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_2_3 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 3 4 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_2_4 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 3 5 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_3_0 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 4 1 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_3_1 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 4 2 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_3_2 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 4 3 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_3_3 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 4 4 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_3_4 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 4 5 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_4_0 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 5 1 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_4_1 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 5 2 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_4_2 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 5 3 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_4_3 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 5 4 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151_4_4 :
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 5 5 (a+1) (c+1) degreeRows151_0 degreeP151 := by
  decide +kernel

lemma degreeCheck151 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows151_0.length, ∀ c ∈ List.range degreeRows151_0.length,
      residualCheck 151 14 23 (d+1) (e+1) (a+1) (c+1) degreeRows151_0 degreeP151 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck151_0_0
  · exact degreeCheck151_0_1
  · exact degreeCheck151_0_2
  · exact degreeCheck151_0_3
  · exact degreeCheck151_0_4
  · exact degreeCheck151_1_0
  · exact degreeCheck151_1_1
  · exact degreeCheck151_1_2
  · exact degreeCheck151_1_3
  · exact degreeCheck151_1_4
  · exact degreeCheck151_2_0
  · exact degreeCheck151_2_1
  · exact degreeCheck151_2_2
  · exact degreeCheck151_2_3
  · exact degreeCheck151_2_4
  · exact degreeCheck151_3_0
  · exact degreeCheck151_3_1
  · exact degreeCheck151_3_2
  · exact degreeCheck151_3_3
  · exact degreeCheck151_3_4
  · exact degreeCheck151_4_0
  · exact degreeCheck151_4_1
  · exact degreeCheck151_4_2
  · exact degreeCheck151_4_3
  · exact degreeCheck151_4_4

lemma degree_pos151 (μ : YoungDiagram) (hμ : μ.card = 151) :
    0 < kronecker (canonicalTableau (candidate 14 11 1) degreeCard151)
      (canonicalTableau (candidate 14 11 1) degreeCard151) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 23) (by decide) (by decide) rfl (by decide)
    degreeCard151 degreeRows151_0 (by decide) (by decide)
    degreePlan151_0 (by decide) (by decide) (by decide) (by decide) degreeP151 ?_
    degreeCheck151 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard151 rfl degreeCones151
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
