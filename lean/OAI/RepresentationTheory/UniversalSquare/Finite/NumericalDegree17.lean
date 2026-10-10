import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard17 : (candidate 5 0 1).card = 17 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan17_0 : PackingPlan := (.join (.twoPaths 4 [3,3,3,3]) (.neighbor 2 [2,1,1,1]))
def degreeRows17_0 : List ℕ := [3,3,3,3,2,1,1,1]

lemma degreeCone17_0 (μ : YoungDiagram) (hμ : μ.card = 17)
    (hd : RowsDom μ.rowLens degreeRows17_0) : SquareOccurs (candidate 5 0 1) μ := by
  exact candidate_cone (by decide) degreeCard17 degreePlan17_0 degreeRows17_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs17 : List (List ℕ) := []

lemma degreeCones17 : ∀ q ∈ degreeQs17, ∀ μ : YoungDiagram, μ.card = 17 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 5 0 1) μ := by
  intro q hq
  simp only [degreeQs17,List.not_mem_nil] at hq

abbrev degreeP17 := ResidualProperty 5 1 degreeQs17 []

lemma degreeCheck17_0_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_0_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_0_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_0_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_0_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 1 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_1_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 2 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_2_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 3 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_3_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 4 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_0 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 1 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_1 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 2 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_2 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 3 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_3 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 4 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17_4_4 :
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 5 5 (a+1) (c+1) degreeRows17_0 degreeP17 := by
  decide +kernel

lemma degreeCheck17 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows17_0.length, ∀ c ∈ List.range degreeRows17_0.length,
      residualCheck 17 5 1 (d+1) (e+1) (a+1) (c+1) degreeRows17_0 degreeP17 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck17_0_0
  · exact degreeCheck17_0_1
  · exact degreeCheck17_0_2
  · exact degreeCheck17_0_3
  · exact degreeCheck17_0_4
  · exact degreeCheck17_1_0
  · exact degreeCheck17_1_1
  · exact degreeCheck17_1_2
  · exact degreeCheck17_1_3
  · exact degreeCheck17_1_4
  · exact degreeCheck17_2_0
  · exact degreeCheck17_2_1
  · exact degreeCheck17_2_2
  · exact degreeCheck17_2_3
  · exact degreeCheck17_2_4
  · exact degreeCheck17_3_0
  · exact degreeCheck17_3_1
  · exact degreeCheck17_3_2
  · exact degreeCheck17_3_3
  · exact degreeCheck17_3_4
  · exact degreeCheck17_4_0
  · exact degreeCheck17_4_1
  · exact degreeCheck17_4_2
  · exact degreeCheck17_4_3
  · exact degreeCheck17_4_4

lemma degree_pos17 (μ : YoungDiagram) (hμ : μ.card = 17) :
    0 < kronecker (canonicalTableau (candidate 5 0 1) degreeCard17)
      (canonicalTableau (candidate 5 0 1) degreeCard17) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard17 degreeRows17_0 (by decide) (by decide)
    degreePlan17_0 (by decide) (by decide) (by decide) (by decide) degreeP17 ?_
    degreeCheck17 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard17 rfl degreeCones17
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
