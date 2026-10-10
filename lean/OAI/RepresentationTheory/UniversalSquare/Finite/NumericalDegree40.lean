import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 40. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard40 : (candidate 8 1 0).card = 40 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan40_0 : PackingPlan := (.join (.neighbor 8 [5,4,4,4]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 2 1 [3,2]))))
def degreeRows40_0 : List ℕ := [5,4,4,4,3,3,3,3,2,2,2,2,2,1]

lemma degreeCone40_0 (μ : YoungDiagram) (hμ : μ.card = 40)
    (hd : RowsDom μ.rowLens degreeRows40_0) : SquareOccurs (candidate 8 1 0) μ := by
  exact candidate_cone (by decide) degreeCard40 degreePlan40_0 degreeRows40_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs40 : List (List ℕ) := []

lemma degreeCones40 : ∀ q ∈ degreeQs40, ∀ μ : YoungDiagram, μ.card = 40 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 1 0) μ := by
  intro q hq
  simp only [degreeQs40, List.not_mem_nil] at hq

abbrev degreeP40 := ResidualProperty 8 2 degreeQs40 []

lemma degreeCheck40_0_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_0_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_0_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_0_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_0_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 1 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_1_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 2 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_2_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 3 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_3_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 4 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_0 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 1 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_1 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 2 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_2 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 3 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_3 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 4 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40_4_4 :
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 5 5 (a+1) (c+1) degreeRows40_0 degreeP40 := by
  decide +kernel

lemma degreeCheck40 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows40_0.length, ∀ c ∈ List.range degreeRows40_0.length,
      residualCheck 40 8 2 (d+1) (e+1) (a+1) (c+1) degreeRows40_0 degreeP40 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck40_0_0
  · exact degreeCheck40_0_1
  · exact degreeCheck40_0_2
  · exact degreeCheck40_0_3
  · exact degreeCheck40_0_4
  · exact degreeCheck40_1_0
  · exact degreeCheck40_1_1
  · exact degreeCheck40_1_2
  · exact degreeCheck40_1_3
  · exact degreeCheck40_1_4
  · exact degreeCheck40_2_0
  · exact degreeCheck40_2_1
  · exact degreeCheck40_2_2
  · exact degreeCheck40_2_3
  · exact degreeCheck40_2_4
  · exact degreeCheck40_3_0
  · exact degreeCheck40_3_1
  · exact degreeCheck40_3_2
  · exact degreeCheck40_3_3
  · exact degreeCheck40_3_4
  · exact degreeCheck40_4_0
  · exact degreeCheck40_4_1
  · exact degreeCheck40_4_2
  · exact degreeCheck40_4_3
  · exact degreeCheck40_4_4

lemma degree_pos40 (μ : YoungDiagram) (hμ : μ.card = 40) :
    0 < kronecker (canonicalTableau (candidate 8 1 0) degreeCard40)
      (canonicalTableau (candidate 8 1 0) degreeCard40) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard40 degreeRows40_0 (by decide) (by decide)
    degreePlan40_0 (by decide) (by decide) (by decide) (by decide) degreeP40 ?_
    degreeCheck40 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard40 rfl degreeCones40
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
