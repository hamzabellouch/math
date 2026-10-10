import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 60. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard60 : (candidate 8 6 0).card = 60 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan60_0 : PackingPlan := (.join (.neighbor 13 [7,7,7,6]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 7 1 [8,7]))))
def degreeRows60_0 : List ℕ := [8,7,7,7,7,6,3,3,3,2,2,2,2,1]

lemma degreeCone60_0 (μ : YoungDiagram) (hμ : μ.card = 60)
    (hd : RowsDom μ.rowLens degreeRows60_0) : SquareOccurs (candidate 8 6 0) μ := by
  exact candidate_cone (by decide) degreeCard60 degreePlan60_0 degreeRows60_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs60 : List (List ℕ) := []

lemma degreeCones60 : ∀ q ∈ degreeQs60, ∀ μ : YoungDiagram, μ.card = 60 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 6 0) μ := by
  intro q hq
  simp only [degreeQs60,List.not_mem_nil] at hq

abbrev degreeP60 := ResidualProperty 8 12 degreeQs60 []

lemma degreeCheck60_0_0 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 1 1 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_0_1 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 1 2 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_0_2 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 1 3 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_0_3 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 1 4 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_0_4 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 1 5 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_1_0 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 2 1 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_1_1 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 2 2 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_1_2 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 2 3 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_1_3 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 2 4 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_1_4 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 2 5 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_2_0 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 3 1 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_2_1 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 3 2 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_2_2 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 3 3 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_2_3 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 3 4 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_2_4 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 3 5 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_3_0 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 4 1 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_3_1 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 4 2 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_3_2 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 4 3 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_3_3 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 4 4 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_3_4 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 4 5 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_4_0 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 5 1 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_4_1 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 5 2 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_4_2 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 5 3 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_4_3 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 5 4 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60_4_4 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 5 5 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

lemma degreeCheck60 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 (d+1) (e+1) (a+1) (c+1) degreeRows60_0 degreeP60 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck60_0_0
  · exact degreeCheck60_0_1
  · exact degreeCheck60_0_2
  · exact degreeCheck60_0_3
  · exact degreeCheck60_0_4
  · exact degreeCheck60_1_0
  · exact degreeCheck60_1_1
  · exact degreeCheck60_1_2
  · exact degreeCheck60_1_3
  · exact degreeCheck60_1_4
  · exact degreeCheck60_2_0
  · exact degreeCheck60_2_1
  · exact degreeCheck60_2_2
  · exact degreeCheck60_2_3
  · exact degreeCheck60_2_4
  · exact degreeCheck60_3_0
  · exact degreeCheck60_3_1
  · exact degreeCheck60_3_2
  · exact degreeCheck60_3_3
  · exact degreeCheck60_3_4
  · exact degreeCheck60_4_0
  · exact degreeCheck60_4_1
  · exact degreeCheck60_4_2
  · exact degreeCheck60_4_3
  · exact degreeCheck60_4_4

lemma degree_pos60 (μ : YoungDiagram) (hμ : μ.card = 60) :
    0 < kronecker (canonicalTableau (candidate 8 6 0) degreeCard60)
      (canonicalTableau (candidate 8 6 0) degreeCard60) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 12) (by decide) (by decide) rfl (by decide)
    degreeCard60 degreeRows60_0 (by decide) (by decide)
    degreePlan60_0 (by decide) (by decide) (by decide) (by decide) degreeP60 ?_
    degreeCheck60 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard60 rfl degreeCones60
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
