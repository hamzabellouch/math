import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 44. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard44 : (candidate 8 2 0).card = 44 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan44_0 : PackingPlan := (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 3 1 [4,3]))))
def degreeRows44_0 : List ℕ := [5,5,5,4,4,3,3,3,3,2,2,2,2,1]

lemma degreeCone44_0 (μ : YoungDiagram) (hμ : μ.card = 44)
    (hd : RowsDom μ.rowLens degreeRows44_0) : SquareOccurs (candidate 8 2 0) μ := by
  exact candidate_cone (by decide) degreeCard44 degreePlan44_0 degreeRows44_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs44 : List (List ℕ) := []

lemma degreeCones44 : ∀ q ∈ degreeQs44, ∀ μ : YoungDiagram, μ.card = 44 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 2 0) μ := by
  intro q hq
  simp only [degreeQs44,List.not_mem_nil] at hq

abbrev degreeP44 := ResidualProperty 8 4 degreeQs44 []

lemma degreeCheck44_0_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_0_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_0_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_0_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_0_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 1 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_1_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 2 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_2_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 3 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_3_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 4 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_0 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 1 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_1 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 2 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_2 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 3 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_3 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 4 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44_4_4 :
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 5 5 (a+1) (c+1) degreeRows44_0 degreeP44 := by
  decide +kernel

lemma degreeCheck44 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows44_0.length, ∀ c ∈ List.range degreeRows44_0.length,
      residualCheck 44 8 4 (d+1) (e+1) (a+1) (c+1) degreeRows44_0 degreeP44 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck44_0_0
  · exact degreeCheck44_0_1
  · exact degreeCheck44_0_2
  · exact degreeCheck44_0_3
  · exact degreeCheck44_0_4
  · exact degreeCheck44_1_0
  · exact degreeCheck44_1_1
  · exact degreeCheck44_1_2
  · exact degreeCheck44_1_3
  · exact degreeCheck44_1_4
  · exact degreeCheck44_2_0
  · exact degreeCheck44_2_1
  · exact degreeCheck44_2_2
  · exact degreeCheck44_2_3
  · exact degreeCheck44_2_4
  · exact degreeCheck44_3_0
  · exact degreeCheck44_3_1
  · exact degreeCheck44_3_2
  · exact degreeCheck44_3_3
  · exact degreeCheck44_3_4
  · exact degreeCheck44_4_0
  · exact degreeCheck44_4_1
  · exact degreeCheck44_4_2
  · exact degreeCheck44_4_3
  · exact degreeCheck44_4_4

lemma degree_pos44 (μ : YoungDiagram) (hμ : μ.card = 44) :
    0 < kronecker (canonicalTableau (candidate 8 2 0) degreeCard44)
      (canonicalTableau (candidate 8 2 0) degreeCard44) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard44 degreeRows44_0 (by decide) (by decide)
    degreePlan44_0 (by decide) (by decide) (by decide) (by decide) degreeP44 ?_
    degreeCheck44 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard44 rfl degreeCones44
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
