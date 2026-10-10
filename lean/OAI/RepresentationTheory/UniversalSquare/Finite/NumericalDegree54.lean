import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 54. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard54 : (candidate 8 4 1).card = 54 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan54_0 : PackingPlan := (.join (.twoPaths 11 [7,7,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 5 3 [7,6]))))
def degreeRows54_0 : List ℕ := [7,7,7,6,6,6,4,3,3,3,2]

lemma degreeCone54_0 (μ : YoungDiagram) (hμ : μ.card = 54)
    (hd : RowsDom μ.rowLens degreeRows54_0) : SquareOccurs (candidate 8 4 1) μ := by
  exact candidate_cone (by decide) degreeCard54 degreePlan54_0 degreeRows54_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan54_1 : PackingPlan := (.join (.twoPaths 11 [7,7,6,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 5 2))))
def degreeRows54_1 : List ℕ := [10,7,7,6,6,3,3,3,2,2,2,2,1]

lemma degreeCone54_1 (μ : YoungDiagram) (hμ : μ.card = 54)
    (hd : RowsDom μ.rowLens degreeRows54_1) : SquareOccurs (candidate 8 4 1) μ := by
  exact candidate_cone (by decide) degreeCard54 degreePlan54_1 degreeRows54_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs54 : List (List ℕ) := [degreeRows54_1]

lemma degreeCones54 : ∀ q ∈ degreeQs54, ∀ μ : YoungDiagram, μ.card = 54 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 4 1) μ := by
  intro q hq
  simp only [degreeQs54,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone54_1

abbrev degreeP54 := ResidualProperty 8 9 degreeQs54 []

lemma degreeCheck54_0_0 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 1 1 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_0_1 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 1 2 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_0_2 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 1 3 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_0_3 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 1 4 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_0_4 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 1 5 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_1_0 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 2 1 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_1_1 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 2 2 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_1_2 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 2 3 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_1_3 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 2 4 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_1_4 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 2 5 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_2_0 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 3 1 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_2_1 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 3 2 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_2_2 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 3 3 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_2_3 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 3 4 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_2_4 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 3 5 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_3_0 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 4 1 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_3_1 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 4 2 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_3_2 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 4 3 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_3_3 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 4 4 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_3_4 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 4 5 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_0 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 1 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_1 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 2 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_2 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 3 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_3 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 4 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54_4_4 :
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 5 5 (a+1) (c+1) degreeRows54_0 degreeP54 := by
  decide +kernel

lemma degreeCheck54 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows54_0.length, ∀ c ∈ List.range degreeRows54_0.length,
      residualCheck 54 8 9 (d+1) (e+1) (a+1) (c+1) degreeRows54_0 degreeP54 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck54_0_0
  · exact degreeCheck54_0_1
  · exact degreeCheck54_0_2
  · exact degreeCheck54_0_3
  · exact degreeCheck54_0_4
  · exact degreeCheck54_1_0
  · exact degreeCheck54_1_1
  · exact degreeCheck54_1_2
  · exact degreeCheck54_1_3
  · exact degreeCheck54_1_4
  · exact degreeCheck54_2_0
  · exact degreeCheck54_2_1
  · exact degreeCheck54_2_2
  · exact degreeCheck54_2_3
  · exact degreeCheck54_2_4
  · exact degreeCheck54_3_0
  · exact degreeCheck54_3_1
  · exact degreeCheck54_3_2
  · exact degreeCheck54_3_3
  · exact degreeCheck54_3_4
  · exact degreeCheck54_4_0
  · exact degreeCheck54_4_1
  · exact degreeCheck54_4_2
  · exact degreeCheck54_4_3
  · exact degreeCheck54_4_4

lemma degree_pos54 (μ : YoungDiagram) (hμ : μ.card = 54) :
    0 < kronecker (canonicalTableau (candidate 8 4 1) degreeCard54)
      (canonicalTableau (candidate 8 4 1) degreeCard54) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 9) (by decide) (by decide) rfl (by decide)
    degreeCard54 degreeRows54_0 (by decide) (by decide)
    degreePlan54_0 (by decide) (by decide) (by decide) (by decide) degreeP54 ?_
    degreeCheck54 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard54 rfl degreeCones54
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
