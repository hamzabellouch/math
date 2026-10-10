import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard23 : (candidate 6 0 1).card = 23 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan23_0 : PackingPlan := (.join (.twoPaths 5 [4,4,3,3]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 1 2)))
def degreeRows23_0 : List ℕ := [4,4,3,3,2,2,2,2,1]

lemma degreeCone23_0 (μ : YoungDiagram) (hμ : μ.card = 23)
    (hd : RowsDom μ.rowLens degreeRows23_0) : SquareOccurs (candidate 6 0 1) μ := by
  exact candidate_cone (by decide) degreeCard23 degreePlan23_0 degreeRows23_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan23_1 : PackingPlan := (.join (.repeated 1 7) (.join (.neighbor 4 [3,2,2,2]) (.join (.neighbor 2 [2,1,1,1]) (.repeated 2 1))))
def degreeRows23_1 : List ℕ := [7,3,2,2,2,2,2,1,1,1]

lemma degreeCone23_1 (μ : YoungDiagram) (hμ : μ.card = 23)
    (hd : RowsDom μ.rowLens degreeRows23_1) : SquareOccurs (candidate 6 0 1) μ := by
  exact candidate_cone (by decide) degreeCard23 degreePlan23_1 degreeRows23_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs23 : List (List ℕ) := [degreeRows23_1]

lemma degreeCones23 : ∀ q ∈ degreeQs23, ∀ μ : YoungDiagram, μ.card = 23 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 0 1) μ := by
  intro q hq
  simp only [degreeQs23,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone23_1

abbrev degreeP23 := ResidualProperty 6 1 degreeQs23 []

lemma degreeCheck23_0_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_0_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_0_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_0_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_0_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 1 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_1_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 2 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_2_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 3 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_3_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 4 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_0 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 1 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_1 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 2 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_2 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 3 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_3 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 4 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23_4_4 :
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 5 5 (a+1) (c+1) degreeRows23_0 degreeP23 := by
  decide +kernel

lemma degreeCheck23 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows23_0.length, ∀ c ∈ List.range degreeRows23_0.length,
      residualCheck 23 6 1 (d+1) (e+1) (a+1) (c+1) degreeRows23_0 degreeP23 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck23_0_0
  · exact degreeCheck23_0_1
  · exact degreeCheck23_0_2
  · exact degreeCheck23_0_3
  · exact degreeCheck23_0_4
  · exact degreeCheck23_1_0
  · exact degreeCheck23_1_1
  · exact degreeCheck23_1_2
  · exact degreeCheck23_1_3
  · exact degreeCheck23_1_4
  · exact degreeCheck23_2_0
  · exact degreeCheck23_2_1
  · exact degreeCheck23_2_2
  · exact degreeCheck23_2_3
  · exact degreeCheck23_2_4
  · exact degreeCheck23_3_0
  · exact degreeCheck23_3_1
  · exact degreeCheck23_3_2
  · exact degreeCheck23_3_3
  · exact degreeCheck23_3_4
  · exact degreeCheck23_4_0
  · exact degreeCheck23_4_1
  · exact degreeCheck23_4_2
  · exact degreeCheck23_4_3
  · exact degreeCheck23_4_4

lemma degree_pos23 (μ : YoungDiagram) (hμ : μ.card = 23) :
    0 < kronecker (canonicalTableau (candidate 6 0 1) degreeCard23)
      (canonicalTableau (candidate 6 0 1) degreeCard23) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard23 degreeRows23_0 (by decide) (by decide)
    degreePlan23_0 (by decide) (by decide) (by decide) (by decide) degreeP23 ?_
    degreeCheck23 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard23 rfl degreeCones23
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
