import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard33 : (candidate 6 3 0).card = 33 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan33_0 : PackingPlan := (.join (.neighbor 8 [5,4,4,4]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 4 1 [5,4])))
def degreeRows33_0 : List ℕ := [5,5,4,4,4,4,2,2,2,1]

lemma degreeCone33_0 (μ : YoungDiagram) (hμ : μ.card = 33)
    (hd : RowsDom μ.rowLens degreeRows33_0) : SquareOccurs (candidate 6 3 0) μ := by
  exact candidate_cone (by decide) degreeCard33 degreePlan33_0 degreeRows33_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs33 : List (List ℕ) := []

lemma degreeCones33 : ∀ q ∈ degreeQs33, ∀ μ : YoungDiagram, μ.card = 33 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 3 0) μ := by
  intro q hq
  simp only [degreeQs33,List.not_mem_nil] at hq

abbrev degreeP33 := ResidualProperty 6 6 degreeQs33 []

lemma degreeCheck33_0_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_0_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_0_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_0_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_0_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 1 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_1_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 2 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_2_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 3 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_3_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 4 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_0 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 1 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_1 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 2 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_2 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 3 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_3 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 4 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33_4_4 :
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 5 5 (a+1) (c+1) degreeRows33_0 degreeP33 := by
  decide +kernel

lemma degreeCheck33 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows33_0.length, ∀ c ∈ List.range degreeRows33_0.length,
      residualCheck 33 6 6 (d+1) (e+1) (a+1) (c+1) degreeRows33_0 degreeP33 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck33_0_0
  · exact degreeCheck33_0_1
  · exact degreeCheck33_0_2
  · exact degreeCheck33_0_3
  · exact degreeCheck33_0_4
  · exact degreeCheck33_1_0
  · exact degreeCheck33_1_1
  · exact degreeCheck33_1_2
  · exact degreeCheck33_1_3
  · exact degreeCheck33_1_4
  · exact degreeCheck33_2_0
  · exact degreeCheck33_2_1
  · exact degreeCheck33_2_2
  · exact degreeCheck33_2_3
  · exact degreeCheck33_2_4
  · exact degreeCheck33_3_0
  · exact degreeCheck33_3_1
  · exact degreeCheck33_3_2
  · exact degreeCheck33_3_3
  · exact degreeCheck33_3_4
  · exact degreeCheck33_4_0
  · exact degreeCheck33_4_1
  · exact degreeCheck33_4_2
  · exact degreeCheck33_4_3
  · exact degreeCheck33_4_4

lemma degree_pos33 (μ : YoungDiagram) (hμ : μ.card = 33) :
    0 < kronecker (canonicalTableau (candidate 6 3 0) degreeCard33)
      (canonicalTableau (candidate 6 3 0) degreeCard33) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 6) (by decide) (by decide) rfl (by decide)
    degreeCard33 degreeRows33_0 (by decide) (by decide)
    degreePlan33_0 (by decide) (by decide) (by decide) (by decide) degreeP33 ?_
    degreeCheck33 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard33 rfl degreeCones33
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
