import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 112. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard112 : (candidate 12 8 1).card = 112 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan112_0 : PackingPlan := (.join (.twoPaths 19 [11,11,10,10]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 9 3 [11,10]))))))
def degreeRows112_0 : List ℕ := [11,11,11,10,10,10,5,5,5,4,4,4,4,4,3,3,3,3,2]

lemma degreeCone112_0 (μ : YoungDiagram) (hμ : μ.card = 112)
    (hd : RowsDom μ.rowLens degreeRows112_0) : SquareOccurs (candidate 12 8 1) μ := by
  exact candidate_cone (by decide) degreeCard112 degreePlan112_0 degreeRows112_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan112_1 : PackingPlan := (.join (.twoPaths 19 [11,11,10,10]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 9 2))))))
def degreeRows112_1 : List ℕ := [18,11,11,10,10,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

lemma degreeCone112_1 (μ : YoungDiagram) (hμ : μ.card = 112)
    (hd : RowsDom μ.rowLens degreeRows112_1) : SquareOccurs (candidate 12 8 1) μ := by
  exact candidate_cone (by decide) degreeCard112 degreePlan112_1 degreeRows112_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs112 : List (List ℕ) := [degreeRows112_1]

lemma degreeCones112 : ∀ q ∈ degreeQs112, ∀ μ : YoungDiagram, μ.card = 112 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 12 8 1) μ := by
  intro q hq
  simp only [degreeQs112,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone112_1

abbrev degreeP112 := ResidualProperty 12 17 degreeQs112 []

lemma degreeCheck112_0_0 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 1 1 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_0_1 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 1 2 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_0_2 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 1 3 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_0_3 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 1 4 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_0_4 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 1 5 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_1_0 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 2 1 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_1_1 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 2 2 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_1_2 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 2 3 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_1_3 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 2 4 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_1_4 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 2 5 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_2_0 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 3 1 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_2_1 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 3 2 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_2_2 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 3 3 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_2_3 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 3 4 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_2_4 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 3 5 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_3_0 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 4 1 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_3_1 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 4 2 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_3_2 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 4 3 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_3_3 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 4 4 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_3_4 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 4 5 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_4_0 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 5 1 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_4_1 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 5 2 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_4_2 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 5 3 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_4_3 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 5 4 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112_4_4 :
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 5 5 (a+1) (c+1) degreeRows112_0 degreeP112 := by
  decide +kernel

lemma degreeCheck112 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows112_0.length, ∀ c ∈ List.range degreeRows112_0.length,
      residualCheck 112 12 17 (d+1) (e+1) (a+1) (c+1) degreeRows112_0 degreeP112 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck112_0_0
  · exact degreeCheck112_0_1
  · exact degreeCheck112_0_2
  · exact degreeCheck112_0_3
  · exact degreeCheck112_0_4
  · exact degreeCheck112_1_0
  · exact degreeCheck112_1_1
  · exact degreeCheck112_1_2
  · exact degreeCheck112_1_3
  · exact degreeCheck112_1_4
  · exact degreeCheck112_2_0
  · exact degreeCheck112_2_1
  · exact degreeCheck112_2_2
  · exact degreeCheck112_2_3
  · exact degreeCheck112_2_4
  · exact degreeCheck112_3_0
  · exact degreeCheck112_3_1
  · exact degreeCheck112_3_2
  · exact degreeCheck112_3_3
  · exact degreeCheck112_3_4
  · exact degreeCheck112_4_0
  · exact degreeCheck112_4_1
  · exact degreeCheck112_4_2
  · exact degreeCheck112_4_3
  · exact degreeCheck112_4_4

lemma degree_pos112 (μ : YoungDiagram) (hμ : μ.card = 112) :
    0 < kronecker (canonicalTableau (candidate 12 8 1) degreeCard112)
      (canonicalTableau (candidate 12 8 1) degreeCard112) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 17) (by decide) (by decide) rfl (by decide)
    degreeCard112 degreeRows112_0 (by decide) (by decide)
    degreePlan112_0 (by decide) (by decide) (by decide) (by decide) degreeP112 ?_
    degreeCheck112 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard112 rfl degreeCones112
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
