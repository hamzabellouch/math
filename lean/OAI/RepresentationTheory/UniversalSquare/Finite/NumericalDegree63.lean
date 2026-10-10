import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard63 : (candidate 10 2 0).card = 63 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan63_0 : PackingPlan := (.join (.neighbor 11 [6,6,6,5]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 3 1 [4,3])))))
def degreeRows63_0 : List ℕ := [6,6,6,5,4,4,4,4,3,3,3,3,3,2,2,2,2,1]

lemma degreeCone63_0 (μ : YoungDiagram) (hμ : μ.card = 63)
    (hd : RowsDom μ.rowLens degreeRows63_0) : SquareOccurs (candidate 10 2 0) μ := by
  exact candidate_cone (by decide) degreeCard63 degreePlan63_0 degreeRows63_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs63 : List (List ℕ) := []

lemma degreeCones63 : ∀ q ∈ degreeQs63, ∀ μ : YoungDiagram, μ.card = 63 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 10 2 0) μ := by
  intro q hq
  simp only [degreeQs63, List.not_mem_nil] at hq

abbrev degreeP63 := ResidualProperty 10 4 degreeQs63 []

lemma degreeCheck63_0_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_0_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_0_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_0_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_0_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 1 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_1_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 2 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_2_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 3 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_3_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 4 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_0 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 1 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_1 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 2 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_2 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 3 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_3 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 4 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63_4_4 :
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 5 5 (a+1) (c+1) degreeRows63_0 degreeP63 := by
  decide +kernel

lemma degreeCheck63 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows63_0.length, ∀ c ∈ List.range degreeRows63_0.length,
      residualCheck 63 10 4 (d+1) (e+1) (a+1) (c+1) degreeRows63_0 degreeP63 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck63_0_0
  · exact degreeCheck63_0_1
  · exact degreeCheck63_0_2
  · exact degreeCheck63_0_3
  · exact degreeCheck63_0_4
  · exact degreeCheck63_1_0
  · exact degreeCheck63_1_1
  · exact degreeCheck63_1_2
  · exact degreeCheck63_1_3
  · exact degreeCheck63_1_4
  · exact degreeCheck63_2_0
  · exact degreeCheck63_2_1
  · exact degreeCheck63_2_2
  · exact degreeCheck63_2_3
  · exact degreeCheck63_2_4
  · exact degreeCheck63_3_0
  · exact degreeCheck63_3_1
  · exact degreeCheck63_3_2
  · exact degreeCheck63_3_3
  · exact degreeCheck63_3_4
  · exact degreeCheck63_4_0
  · exact degreeCheck63_4_1
  · exact degreeCheck63_4_2
  · exact degreeCheck63_4_3
  · exact degreeCheck63_4_4

lemma degree_pos63 (μ : YoungDiagram) (hμ : μ.card = 63) :
    0 < kronecker (canonicalTableau (candidate 10 2 0) degreeCard63)
      (canonicalTableau (candidate 10 2 0) degreeCard63) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard63 degreeRows63_0 (by decide) (by decide)
    degreePlan63_0 (by decide) (by decide) (by decide) (by decide) degreeP63 ?_
    degreeCheck63 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard63 rfl degreeCones63
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
