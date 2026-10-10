import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard59 : (candidate 10 1 0).card = 59 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan59_0 : PackingPlan := (.join (.neighbor 10 [6,5,5,5]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 2 1 [3,2])))))
def degreeRows59_0 : List ℕ := [6,5,5,5,4,4,4,3,3,3,3,3,2,2,2,2,2,1]

lemma degreeCone59_0 (μ : YoungDiagram) (hμ : μ.card = 59)
    (hd : RowsDom μ.rowLens degreeRows59_0) : SquareOccurs (candidate 10 1 0) μ := by
  exact candidate_cone (by decide) degreeCard59 degreePlan59_0 degreeRows59_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs59 : List (List ℕ) := []

lemma degreeCones59 : ∀ q ∈ degreeQs59, ∀ μ : YoungDiagram, μ.card = 59 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 10 1 0) μ := by
  intro q hq
  simp only [degreeQs59,List.not_mem_nil] at hq

abbrev degreeP59 := ResidualProperty 10 2 degreeQs59 []

lemma degreeCheck59_0_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_0_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_0_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_0_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_0_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 1 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_1_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 2 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_2_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 3 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_3_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 4 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_0 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 1 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_1 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 2 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_2 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 3 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_3 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 4 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59_4_4 :
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 5 5 (a+1) (c+1) degreeRows59_0 degreeP59 := by
  decide +kernel

lemma degreeCheck59 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows59_0.length, ∀ c ∈ List.range degreeRows59_0.length,
      residualCheck 59 10 2 (d+1) (e+1) (a+1) (c+1) degreeRows59_0 degreeP59 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck59_0_0
  · exact degreeCheck59_0_1
  · exact degreeCheck59_0_2
  · exact degreeCheck59_0_3
  · exact degreeCheck59_0_4
  · exact degreeCheck59_1_0
  · exact degreeCheck59_1_1
  · exact degreeCheck59_1_2
  · exact degreeCheck59_1_3
  · exact degreeCheck59_1_4
  · exact degreeCheck59_2_0
  · exact degreeCheck59_2_1
  · exact degreeCheck59_2_2
  · exact degreeCheck59_2_3
  · exact degreeCheck59_2_4
  · exact degreeCheck59_3_0
  · exact degreeCheck59_3_1
  · exact degreeCheck59_3_2
  · exact degreeCheck59_3_3
  · exact degreeCheck59_3_4
  · exact degreeCheck59_4_0
  · exact degreeCheck59_4_1
  · exact degreeCheck59_4_2
  · exact degreeCheck59_4_3
  · exact degreeCheck59_4_4

lemma degree_pos59 (μ : YoungDiagram) (hμ : μ.card = 59) :
    0 < kronecker (canonicalTableau (candidate 10 1 0) degreeCard59)
      (canonicalTableau (candidate 10 1 0) degreeCard59) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard59 degreeRows59_0 (by decide) (by decide)
    degreePlan59_0 (by decide) (by decide) (by decide) (by decide) degreeP59 ?_
    degreeCheck59 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard59 rfl degreeCones59
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
