import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard27 : (candidate 6 1 1).card = 27 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan27_0 : PackingPlan := (.join (.twoPaths 6 [4,4,4,4]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 2 2)))
def degreeRows27_0 : List ℕ := [4,4,4,4,4,2,2,2,1]

lemma degreeCone27_0 (μ : YoungDiagram) (hμ : μ.card = 27)
    (hd : RowsDom μ.rowLens degreeRows27_0) : SquareOccurs (candidate 6 1 1) μ := by
  exact candidate_cone (by decide) degreeCard27 degreePlan27_0 degreeRows27_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs27 : List (List ℕ) := []

lemma degreeCones27 : ∀ q ∈ degreeQs27, ∀ μ : YoungDiagram, μ.card = 27 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 1 1) μ := by
  intro q hq
  simp only [degreeQs27,List.not_mem_nil] at hq

abbrev degreeP27 := ResidualProperty 6 3 degreeQs27 []

lemma degreeCheck27_0_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_0_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_0_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_0_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_0_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 1 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_1_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 2 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_2_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 3 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_3_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 4 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_0 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 1 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_1 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 2 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_2 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 3 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_3 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 4 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27_4_4 :
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 5 5 (a+1) (c+1) degreeRows27_0 degreeP27 := by
  decide +kernel

lemma degreeCheck27 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows27_0.length, ∀ c ∈ List.range degreeRows27_0.length,
      residualCheck 27 6 3 (d+1) (e+1) (a+1) (c+1) degreeRows27_0 degreeP27 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck27_0_0
  · exact degreeCheck27_0_1
  · exact degreeCheck27_0_2
  · exact degreeCheck27_0_3
  · exact degreeCheck27_0_4
  · exact degreeCheck27_1_0
  · exact degreeCheck27_1_1
  · exact degreeCheck27_1_2
  · exact degreeCheck27_1_3
  · exact degreeCheck27_1_4
  · exact degreeCheck27_2_0
  · exact degreeCheck27_2_1
  · exact degreeCheck27_2_2
  · exact degreeCheck27_2_3
  · exact degreeCheck27_2_4
  · exact degreeCheck27_3_0
  · exact degreeCheck27_3_1
  · exact degreeCheck27_3_2
  · exact degreeCheck27_3_3
  · exact degreeCheck27_3_4
  · exact degreeCheck27_4_0
  · exact degreeCheck27_4_1
  · exact degreeCheck27_4_2
  · exact degreeCheck27_4_3
  · exact degreeCheck27_4_4

lemma degree_pos27 (μ : YoungDiagram) (hμ : μ.card = 27) :
    0 < kronecker (canonicalTableau (candidate 6 1 1) degreeCard27)
      (canonicalTableau (candidate 6 1 1) degreeCard27) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 3) (by decide) (by decide) rfl (by decide)
    degreeCard27 degreeRows27_0 (by decide) (by decide)
    degreePlan27_0 (by decide) (by decide) (by decide) (by decide) degreeP27 ?_
    degreeCheck27 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard27 rfl degreeCones27
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
