import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard57 : (candidate 10 0 1).card = 57 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan57_0 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 1 2)))))
def degreeRows57_0 : List ℕ := [6,6,5,5,4,4,4,3,3,3,3,2,2,2,2,2,1]

lemma degreeCone57_0 (μ : YoungDiagram) (hμ : μ.card = 57)
    (hd : RowsDom μ.rowLens degreeRows57_0) : SquareOccurs (candidate 10 0 1) μ := by
  exact candidate_cone (by decide) degreeCard57 degreePlan57_0 degreeRows57_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan57_1 : PackingPlan := (.join (.repeated 1 11) (.join (.neighbor 8 [5,4,4,4]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.neighbor 2 [2,1,1,1]) (.repeated 2 1))))))
def degreeRows57_1 : List ℕ := [11,5,4,4,4,4,3,3,3,3,2,2,2,2,2,1,1,1]

lemma degreeCone57_1 (μ : YoungDiagram) (hμ : μ.card = 57)
    (hd : RowsDom μ.rowLens degreeRows57_1) : SquareOccurs (candidate 10 0 1) μ := by
  exact candidate_cone (by decide) degreeCard57 degreePlan57_1 degreeRows57_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs57 : List (List ℕ) := [degreeRows57_1]

lemma degreeCones57 : ∀ q ∈ degreeQs57, ∀ μ : YoungDiagram, μ.card = 57 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 10 0 1) μ := by
  intro q hq
  simp only [degreeQs57,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone57_1

abbrev degreeP57 := ResidualProperty 10 1 degreeQs57 []

lemma degreeCheck57_0_0 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 1 1 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_0_1 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 1 2 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_0_2 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 1 3 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_0_3 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 1 4 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_0_4 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 1 5 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_1_0 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 2 1 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_1_1 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 2 2 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_1_2 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 2 3 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_1_3 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 2 4 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_1_4 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 2 5 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_2_0 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 3 1 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_2_1 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 3 2 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_2_2 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 3 3 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_2_3 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 3 4 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_2_4 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 3 5 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_3_0 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 4 1 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_3_1 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 4 2 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_3_2 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 4 3 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_3_3 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 4 4 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_3_4 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 4 5 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_4_0 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 5 1 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_4_1 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 5 2 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_4_2 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 5 3 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_4_3 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 5 4 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57_4_4 :
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 5 5 (a+1) (c+1) degreeRows57_0 degreeP57 := by
  decide +kernel

lemma degreeCheck57 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows57_0.length, ∀ c ∈ List.range degreeRows57_0.length,
      residualCheck 57 10 1 (d+1) (e+1) (a+1) (c+1) degreeRows57_0 degreeP57 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck57_0_0
  · exact degreeCheck57_0_1
  · exact degreeCheck57_0_2
  · exact degreeCheck57_0_3
  · exact degreeCheck57_0_4
  · exact degreeCheck57_1_0
  · exact degreeCheck57_1_1
  · exact degreeCheck57_1_2
  · exact degreeCheck57_1_3
  · exact degreeCheck57_1_4
  · exact degreeCheck57_2_0
  · exact degreeCheck57_2_1
  · exact degreeCheck57_2_2
  · exact degreeCheck57_2_3
  · exact degreeCheck57_2_4
  · exact degreeCheck57_3_0
  · exact degreeCheck57_3_1
  · exact degreeCheck57_3_2
  · exact degreeCheck57_3_3
  · exact degreeCheck57_3_4
  · exact degreeCheck57_4_0
  · exact degreeCheck57_4_1
  · exact degreeCheck57_4_2
  · exact degreeCheck57_4_3
  · exact degreeCheck57_4_4

lemma degree_pos57 (μ : YoungDiagram) (hμ : μ.card = 57) :
    0 < kronecker (canonicalTableau (candidate 10 0 1) degreeCard57)
      (canonicalTableau (candidate 10 0 1) degreeCard57) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard57 degreeRows57_0 (by decide) (by decide)
    degreePlan57_0 (by decide) (by decide) (by decide) (by decide) degreeP57 ?_
    degreeCheck57 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard57 rfl degreeCones57
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
