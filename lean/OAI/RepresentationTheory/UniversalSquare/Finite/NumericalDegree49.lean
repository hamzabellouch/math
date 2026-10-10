import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 49. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard49 : (candidate 9 1 0).card = 49 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan49_0 : PackingPlan := (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.repeated 1 3) (.twosOdd 2 1 [3,2])))))
def degreeRows49_0 : List ℕ := [5,5,5,4,4,3,3,3,3,3,3,2,2,2,2]

lemma degreeCone49_0 (μ : YoungDiagram) (hμ : μ.card = 49)
    (hd : RowsDom μ.rowLens degreeRows49_0) : SquareOccurs (candidate 9 1 0) μ := by
  exact candidate_cone (by decide) degreeCard49 degreePlan49_0 degreeRows49_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs49 : List (List ℕ) := []

lemma degreeCones49 : ∀ q ∈ degreeQs49, ∀ μ : YoungDiagram, μ.card = 49 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 9 1 0) μ := by
  intro q hq
  simp only [degreeQs49,List.not_mem_nil] at hq

abbrev degreeP49 := ResidualProperty 9 2 degreeQs49 []

lemma degreeCheck49_0_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_0_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_0_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_0_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_0_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 1 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_1_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 2 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_2_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 3 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_3_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 4 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_0 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 1 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_1 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 2 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_2 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 3 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_3 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 4 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49_4_4 :
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 5 5 (a+1) (c+1) degreeRows49_0 degreeP49 := by
  decide +kernel

lemma degreeCheck49 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows49_0.length, ∀ c ∈ List.range degreeRows49_0.length,
      residualCheck 49 9 2 (d+1) (e+1) (a+1) (c+1) degreeRows49_0 degreeP49 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck49_0_0
  · exact degreeCheck49_0_1
  · exact degreeCheck49_0_2
  · exact degreeCheck49_0_3
  · exact degreeCheck49_0_4
  · exact degreeCheck49_1_0
  · exact degreeCheck49_1_1
  · exact degreeCheck49_1_2
  · exact degreeCheck49_1_3
  · exact degreeCheck49_1_4
  · exact degreeCheck49_2_0
  · exact degreeCheck49_2_1
  · exact degreeCheck49_2_2
  · exact degreeCheck49_2_3
  · exact degreeCheck49_2_4
  · exact degreeCheck49_3_0
  · exact degreeCheck49_3_1
  · exact degreeCheck49_3_2
  · exact degreeCheck49_3_3
  · exact degreeCheck49_3_4
  · exact degreeCheck49_4_0
  · exact degreeCheck49_4_1
  · exact degreeCheck49_4_2
  · exact degreeCheck49_4_3
  · exact degreeCheck49_4_4

lemma degree_pos49 (μ : YoungDiagram) (hμ : μ.card = 49) :
    0 < kronecker (canonicalTableau (candidate 9 1 0) degreeCard49)
      (canonicalTableau (candidate 9 1 0) degreeCard49) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard49 degreeRows49_0 (by decide) (by decide)
    degreePlan49_0 (by decide) (by decide) (by decide) (by decide) degreeP49 ?_
    degreeCheck49 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard49 rfl degreeCones49
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
