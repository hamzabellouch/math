import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard42 : (candidate 8 1 1).card = 42 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan42_0 : PackingPlan := (.join (.twoPaths 8 [5,5,5,5]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 2 2))))
def degreeRows42_0 : List ℕ := [5,5,5,5,4,3,3,3,2,2,2,2,1]

lemma degreeCone42_0 (μ : YoungDiagram) (hμ : μ.card = 42)
    (hd : RowsDom μ.rowLens degreeRows42_0) : SquareOccurs (candidate 8 1 1) μ := by
  exact candidate_cone (by decide) degreeCard42 degreePlan42_0 degreeRows42_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs42 : List (List ℕ) := []

lemma degreeCones42 : ∀ q ∈ degreeQs42, ∀ μ : YoungDiagram, μ.card = 42 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 1 1) μ := by
  intro q hq
  simp only [degreeQs42,List.not_mem_nil] at hq

abbrev degreeP42 := ResidualProperty 8 3 degreeQs42 []

lemma degreeCheck42_0_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_0_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_0_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_0_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_0_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 1 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_1_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 2 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_2_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_3_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 4 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_0 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 1 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_1 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 2 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_2 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 3 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42_4_4 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 5 5 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

lemma degreeCheck42 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 (d+1) (e+1) (a+1) (c+1) degreeRows42_0 degreeP42 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck42_0_0
  · exact degreeCheck42_0_1
  · exact degreeCheck42_0_2
  · exact degreeCheck42_0_3
  · exact degreeCheck42_0_4
  · exact degreeCheck42_1_0
  · exact degreeCheck42_1_1
  · exact degreeCheck42_1_2
  · exact degreeCheck42_1_3
  · exact degreeCheck42_1_4
  · exact degreeCheck42_2_0
  · exact degreeCheck42_2_1
  · exact degreeCheck42_2_2
  · exact degreeCheck42_2_3
  · exact degreeCheck42_2_4
  · exact degreeCheck42_3_0
  · exact degreeCheck42_3_1
  · exact degreeCheck42_3_2
  · exact degreeCheck42_3_3
  · exact degreeCheck42_3_4
  · exact degreeCheck42_4_0
  · exact degreeCheck42_4_1
  · exact degreeCheck42_4_2
  · exact degreeCheck42_4_3
  · exact degreeCheck42_4_4

lemma degree_pos42 (μ : YoungDiagram) (hμ : μ.card = 42) :
    0 < kronecker (canonicalTableau (candidate 8 1 1) degreeCard42)
      (canonicalTableau (candidate 8 1 1) degreeCard42) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 3) (by decide) (by decide) rfl (by decide)
    degreeCard42 degreeRows42_0 (by decide) (by decide)
    degreePlan42_0 (by decide) (by decide) (by decide) (by decide) degreeP42 ?_
    degreeCheck42 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard42 rfl degreeCones42
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
