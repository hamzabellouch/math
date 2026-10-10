import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 38. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard38 : (candidate 8 0 1).card = 38 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan38_0 : PackingPlan := (.join (.twoPaths 7 [5,5,4,4]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 1 2))))
def degreeRows38_0 : List ℕ := [5,5,4,4,3,3,3,2,2,2,2,2,1]

lemma degreeCone38_0 (μ : YoungDiagram) (hμ : μ.card = 38)
    (hd : RowsDom μ.rowLens degreeRows38_0) : SquareOccurs (candidate 8 0 1) μ := by
  exact candidate_cone (by decide) degreeCard38 degreePlan38_0 degreeRows38_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan38_1 : PackingPlan := (.join (.repeated 1 9) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.neighbor 2 [2,1,1,1]) (.repeated 2 1)))))
def degreeRows38_1 : List ℕ := [9,4,3,3,3,3,2,2,2,2,2,1,1,1]

lemma degreeCone38_1 (μ : YoungDiagram) (hμ : μ.card = 38)
    (hd : RowsDom μ.rowLens degreeRows38_1) : SquareOccurs (candidate 8 0 1) μ := by
  exact candidate_cone (by decide) degreeCard38 degreePlan38_1 degreeRows38_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs38 : List (List ℕ) := [degreeRows38_1]

lemma degreeCones38 : ∀ q ∈ degreeQs38, ∀ μ : YoungDiagram, μ.card = 38 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 0 1) μ := by
  intro q hq
  simp only [degreeQs38,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone38_1

abbrev degreeP38 := ResidualProperty 8 1 degreeQs38 []

lemma degreeCheck38_0_0 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 1 1 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_0_1 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 1 2 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_0_2 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 1 3 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_0_3 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 1 4 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_0_4 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 1 5 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_1_0 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 2 1 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_1_1 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 2 2 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_1_2 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 2 3 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_1_3 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 2 4 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_1_4 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 2 5 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_2_0 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 3 1 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_2_1 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 3 2 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_2_2 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 3 3 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_2_3 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 3 4 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_2_4 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 3 5 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_3_0 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 4 1 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_3_1 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 4 2 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_3_2 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 4 3 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_3_3 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 4 4 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_3_4 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 4 5 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_4_0 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 5 1 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_4_1 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 5 2 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_4_2 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 5 3 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_4_3 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 5 4 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38_4_4 :
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 5 5 (a+1) (c+1) degreeRows38_0 degreeP38 := by
  decide +kernel

lemma degreeCheck38 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows38_0.length, ∀ c ∈ List.range degreeRows38_0.length,
      residualCheck 38 8 1 (d+1) (e+1) (a+1) (c+1) degreeRows38_0 degreeP38 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck38_0_0
  · exact degreeCheck38_0_1
  · exact degreeCheck38_0_2
  · exact degreeCheck38_0_3
  · exact degreeCheck38_0_4
  · exact degreeCheck38_1_0
  · exact degreeCheck38_1_1
  · exact degreeCheck38_1_2
  · exact degreeCheck38_1_3
  · exact degreeCheck38_1_4
  · exact degreeCheck38_2_0
  · exact degreeCheck38_2_1
  · exact degreeCheck38_2_2
  · exact degreeCheck38_2_3
  · exact degreeCheck38_2_4
  · exact degreeCheck38_3_0
  · exact degreeCheck38_3_1
  · exact degreeCheck38_3_2
  · exact degreeCheck38_3_3
  · exact degreeCheck38_3_4
  · exact degreeCheck38_4_0
  · exact degreeCheck38_4_1
  · exact degreeCheck38_4_2
  · exact degreeCheck38_4_3
  · exact degreeCheck38_4_4

lemma degree_pos38 (μ : YoungDiagram) (hμ : μ.card = 38) :
    0 < kronecker (canonicalTableau (candidate 8 0 1) degreeCard38)
      (canonicalTableau (candidate 8 0 1) degreeCard38) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard38 degreeRows38_0 (by decide) (by decide)
    degreePlan38_0 (by decide) (by decide) (by decide) (by decide) degreeP38 ?_
    degreeCheck38 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard38 rfl degreeCones38
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
