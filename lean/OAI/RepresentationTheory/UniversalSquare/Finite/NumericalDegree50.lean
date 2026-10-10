import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 50. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard50 : (candidate 8 3 1).card = 50 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan50_0 : PackingPlan := (.join (.twoPaths 10 [6,6,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 4 3 [6,5]))))
def degreeRows50_0 : List ℕ := [6,6,6,6,6,5,4,3,3,3,2]

lemma degreeCone50_0 (μ : YoungDiagram) (hμ : μ.card = 50)
    (hd : RowsDom μ.rowLens degreeRows50_0) : SquareOccurs (candidate 8 3 1) μ := by
  exact candidate_cone (by decide) degreeCard50 degreePlan50_0 degreeRows50_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan50_1 : PackingPlan := (.join (.twoPaths 10 [6,6,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 4 2))))
def degreeRows50_1 : List ℕ := [8,6,6,6,6,3,3,3,2,2,2,2,1]

lemma degreeCone50_1 (μ : YoungDiagram) (hμ : μ.card = 50)
    (hd : RowsDom μ.rowLens degreeRows50_1) : SquareOccurs (candidate 8 3 1) μ := by
  exact candidate_cone (by decide) degreeCard50 degreePlan50_1 degreeRows50_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs50 : List (List ℕ) := [degreeRows50_1]

lemma degreeCones50 : ∀ q ∈ degreeQs50, ∀ μ : YoungDiagram, μ.card = 50 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 3 1) μ := by
  intro q hq
  simp only [degreeQs50,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone50_1

abbrev degreeP50 := ResidualProperty 8 7 degreeQs50 []

lemma degreeCheck50_0_0 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 1 1 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_0_1 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 1 2 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_0_2 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 1 3 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_0_3 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 1 4 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_0_4 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 1 5 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_1_0 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 2 1 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_1_1 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 2 2 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_1_2 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 2 3 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_1_3 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 2 4 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_1_4 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 2 5 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_2_0 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 1 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_2_1 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 2 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_2_2 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 3 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_2_3 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 4 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_2_4 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 3 5 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_0 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 1 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_1 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 2 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_2 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 3 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_3 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 4 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_3_4 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 4 5 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_0 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 1 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_1 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 2 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_2 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 3 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_3 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 4 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50_4_4 :
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 5 5 (a+1) (c+1) degreeRows50_0 degreeP50 := by
  decide +kernel

lemma degreeCheck50 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows50_0.length, ∀ c ∈ List.range degreeRows50_0.length,
      residualCheck 50 8 7 (d+1) (e+1) (a+1) (c+1) degreeRows50_0 degreeP50 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck50_0_0
  · exact degreeCheck50_0_1
  · exact degreeCheck50_0_2
  · exact degreeCheck50_0_3
  · exact degreeCheck50_0_4
  · exact degreeCheck50_1_0
  · exact degreeCheck50_1_1
  · exact degreeCheck50_1_2
  · exact degreeCheck50_1_3
  · exact degreeCheck50_1_4
  · exact degreeCheck50_2_0
  · exact degreeCheck50_2_1
  · exact degreeCheck50_2_2
  · exact degreeCheck50_2_3
  · exact degreeCheck50_2_4
  · exact degreeCheck50_3_0
  · exact degreeCheck50_3_1
  · exact degreeCheck50_3_2
  · exact degreeCheck50_3_3
  · exact degreeCheck50_3_4
  · exact degreeCheck50_4_0
  · exact degreeCheck50_4_1
  · exact degreeCheck50_4_2
  · exact degreeCheck50_4_3
  · exact degreeCheck50_4_4

lemma degree_pos50 (μ : YoungDiagram) (hμ : μ.card = 50) :
    0 < kronecker (canonicalTableau (candidate 8 3 1) degreeCard50)
      (canonicalTableau (candidate 8 3 1) degreeCard50) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 7) (by decide) (by decide) rfl (by decide)
    degreeCard50 degreeRows50_0 (by decide) (by decide)
    degreePlan50_0 (by decide) (by decide) (by decide) (by decide) degreeP50 ?_
    degreeCheck50 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard50 rfl degreeCones50
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
