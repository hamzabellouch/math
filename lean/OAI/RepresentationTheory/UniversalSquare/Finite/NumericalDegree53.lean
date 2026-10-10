import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard53 : (candidate 9 2 0).card = 53 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan53_0 : PackingPlan := (.join (.neighbor 10 [6,5,5,5]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.repeated 1 3) (.twosOdd 3 1 [4,3])))))
def degreeRows53_0 : List ℕ := [6,5,5,5,4,4,3,3,3,3,3,3,2,2,2]

lemma degreeCone53_0 (μ : YoungDiagram) (hμ : μ.card = 53)
    (hd : RowsDom μ.rowLens degreeRows53_0) : SquareOccurs (candidate 9 2 0) μ := by
  exact candidate_cone (by decide) degreeCard53 degreePlan53_0 degreeRows53_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs53 : List (List ℕ) := []

lemma degreeCones53 : ∀ q ∈ degreeQs53, ∀ μ : YoungDiagram, μ.card = 53 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 9 2 0) μ := by
  intro q hq
  simp only [degreeQs53,List.not_mem_nil] at hq

abbrev degreeP53 := ResidualProperty 9 4 degreeQs53 []

lemma degreeCheck53_0_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_0_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_0_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_0_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_0_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 1 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_1_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 2 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_2_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 3 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_3_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 4 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_0 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 1 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_1 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 2 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_2 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 3 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_3 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 4 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53_4_4 :
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 5 5 (a+1) (c+1) degreeRows53_0 degreeP53 := by
  decide +kernel

lemma degreeCheck53 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows53_0.length, ∀ c ∈ List.range degreeRows53_0.length,
      residualCheck 53 9 4 (d+1) (e+1) (a+1) (c+1) degreeRows53_0 degreeP53 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck53_0_0
  · exact degreeCheck53_0_1
  · exact degreeCheck53_0_2
  · exact degreeCheck53_0_3
  · exact degreeCheck53_0_4
  · exact degreeCheck53_1_0
  · exact degreeCheck53_1_1
  · exact degreeCheck53_1_2
  · exact degreeCheck53_1_3
  · exact degreeCheck53_1_4
  · exact degreeCheck53_2_0
  · exact degreeCheck53_2_1
  · exact degreeCheck53_2_2
  · exact degreeCheck53_2_3
  · exact degreeCheck53_2_4
  · exact degreeCheck53_3_0
  · exact degreeCheck53_3_1
  · exact degreeCheck53_3_2
  · exact degreeCheck53_3_3
  · exact degreeCheck53_3_4
  · exact degreeCheck53_4_0
  · exact degreeCheck53_4_1
  · exact degreeCheck53_4_2
  · exact degreeCheck53_4_3
  · exact degreeCheck53_4_4

lemma degree_pos53 (μ : YoungDiagram) (hμ : μ.card = 53) :
    0 < kronecker (canonicalTableau (candidate 9 2 0) degreeCard53)
      (canonicalTableau (candidate 9 2 0) degreeCard53) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard53 degreeRows53_0 (by decide) (by decide)
    degreePlan53_0 (by decide) (by decide) (by decide) (by decide) degreeP53 ?_
    degreeCheck53 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard53 rfl degreeCones53
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
