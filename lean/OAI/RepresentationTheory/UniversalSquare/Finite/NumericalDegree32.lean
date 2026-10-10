import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 32. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard32 : (candidate 7 1 0).card = 32 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan32_0 : PackingPlan := (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.repeated 1 3) (.twosOdd 2 1 [3,2]))))
def degreeRows32_0 : List ℕ := [4,4,4,3,3,3,3,2,2,2,2]

lemma degreeCone32_0 (μ : YoungDiagram) (hμ : μ.card = 32)
    (hd : RowsDom μ.rowLens degreeRows32_0) : SquareOccurs (candidate 7 1 0) μ := by
  exact candidate_cone (by decide) degreeCard32 degreePlan32_0 degreeRows32_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs32 : List (List ℕ) := []

lemma degreeCones32 : ∀ q ∈ degreeQs32, ∀ μ : YoungDiagram, μ.card = 32 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 7 1 0) μ := by
  intro q hq
  simp only [degreeQs32,List.not_mem_nil] at hq

abbrev degreeP32 := ResidualProperty 7 2 degreeQs32 []

lemma degreeCheck32_0_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_0_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_0_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_0_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_0_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 1 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_1_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 2 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_2_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 3 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_3_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 4 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_0 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 1 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_1 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 2 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_2 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 3 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_3 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 4 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32_4_4 :
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 5 5 (a+1) (c+1) degreeRows32_0 degreeP32 := by
  decide +kernel

lemma degreeCheck32 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows32_0.length, ∀ c ∈ List.range degreeRows32_0.length,
      residualCheck 32 7 2 (d+1) (e+1) (a+1) (c+1) degreeRows32_0 degreeP32 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck32_0_0
  · exact degreeCheck32_0_1
  · exact degreeCheck32_0_2
  · exact degreeCheck32_0_3
  · exact degreeCheck32_0_4
  · exact degreeCheck32_1_0
  · exact degreeCheck32_1_1
  · exact degreeCheck32_1_2
  · exact degreeCheck32_1_3
  · exact degreeCheck32_1_4
  · exact degreeCheck32_2_0
  · exact degreeCheck32_2_1
  · exact degreeCheck32_2_2
  · exact degreeCheck32_2_3
  · exact degreeCheck32_2_4
  · exact degreeCheck32_3_0
  · exact degreeCheck32_3_1
  · exact degreeCheck32_3_2
  · exact degreeCheck32_3_3
  · exact degreeCheck32_3_4
  · exact degreeCheck32_4_0
  · exact degreeCheck32_4_1
  · exact degreeCheck32_4_2
  · exact degreeCheck32_4_3
  · exact degreeCheck32_4_4

lemma degree_pos32 (μ : YoungDiagram) (hμ : μ.card = 32) :
    0 < kronecker (canonicalTableau (candidate 7 1 0) degreeCard32)
      (canonicalTableau (candidate 7 1 0) degreeCard32) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard32 degreeRows32_0 (by decide) (by decide)
    degreePlan32_0 (by decide) (by decide) (by decide) (by decide) degreeP32 ?_
    degreeCheck32 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard32 rfl degreeCones32
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
