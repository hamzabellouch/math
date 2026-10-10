import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 30. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard30 : (candidate 7 0 1).card = 30 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan30_0 : PackingPlan := (.join (.twoPaths 6 [4,4,4,4]) (.join (.neighbor 4 [3,2,2,2]) (.neighbor 2 [2,1,1,1])))
def degreeRows30_0 : List ℕ := [4,4,4,4,3,2,2,2,2,1,1,1]

lemma degreeCone30_0 (μ : YoungDiagram) (hμ : μ.card = 30)
    (hd : RowsDom μ.rowLens degreeRows30_0) : SquareOccurs (candidate 7 0 1) μ := by
  exact candidate_cone (by decide) degreeCard30 degreePlan30_0 degreeRows30_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs30 : List (List ℕ) := []

lemma degreeCones30 : ∀ q ∈ degreeQs30, ∀ μ : YoungDiagram, μ.card = 30 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 7 0 1) μ := by
  intro q hq
  simp only [degreeQs30,List.not_mem_nil] at hq

abbrev degreeP30 := ResidualProperty 7 1 degreeQs30 []

lemma degreeCheck30_0_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_0_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_0_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_0_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_0_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 1 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_1_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 2 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_2_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 3 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_3_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 4 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_0 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 1 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_1 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 2 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_2 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 3 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_3 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 4 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30_4_4 :
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 5 5 (a+1) (c+1) degreeRows30_0 degreeP30 := by
  decide +kernel

lemma degreeCheck30 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows30_0.length, ∀ c ∈ List.range degreeRows30_0.length,
      residualCheck 30 7 1 (d+1) (e+1) (a+1) (c+1) degreeRows30_0 degreeP30 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck30_0_0
  · exact degreeCheck30_0_1
  · exact degreeCheck30_0_2
  · exact degreeCheck30_0_3
  · exact degreeCheck30_0_4
  · exact degreeCheck30_1_0
  · exact degreeCheck30_1_1
  · exact degreeCheck30_1_2
  · exact degreeCheck30_1_3
  · exact degreeCheck30_1_4
  · exact degreeCheck30_2_0
  · exact degreeCheck30_2_1
  · exact degreeCheck30_2_2
  · exact degreeCheck30_2_3
  · exact degreeCheck30_2_4
  · exact degreeCheck30_3_0
  · exact degreeCheck30_3_1
  · exact degreeCheck30_3_2
  · exact degreeCheck30_3_3
  · exact degreeCheck30_3_4
  · exact degreeCheck30_4_0
  · exact degreeCheck30_4_1
  · exact degreeCheck30_4_2
  · exact degreeCheck30_4_3
  · exact degreeCheck30_4_4

lemma degree_pos30 (μ : YoungDiagram) (hμ : μ.card = 30) :
    0 < kronecker (canonicalTableau (candidate 7 0 1) degreeCard30)
      (canonicalTableau (candidate 7 0 1) degreeCard30) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard30 degreeRows30_0 (by decide) (by decide)
    degreePlan30_0 (by decide) (by decide) (by decide) (by decide) degreeP30 ?_
    degreeCheck30 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard30 rfl degreeCones30
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
