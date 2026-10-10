import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard25 : (candidate 6 1 0).card = 25 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan25_0 : PackingPlan := (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 2 1 [3,2])))
def degreeRows25_0 : List ℕ := [4,3,3,3,3,2,2,2,2,1]

lemma degreeCone25_0 (μ : YoungDiagram) (hμ : μ.card = 25)
    (hd : RowsDom μ.rowLens degreeRows25_0) : SquareOccurs (candidate 6 1 0) μ := by
  exact candidate_cone (by decide) degreeCard25 degreePlan25_0 degreeRows25_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs25 : List (List ℕ) := []

lemma degreeCones25 : ∀ q ∈ degreeQs25, ∀ μ : YoungDiagram, μ.card = 25 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 1 0) μ := by
  intro q hq
  simp only [degreeQs25,List.not_mem_nil] at hq

abbrev degreeP25 := ResidualProperty 6 2 degreeQs25 []

lemma degreeCheck25_0_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_0_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_0_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_0_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_0_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 1 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_1_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 2 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_2_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 3 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_3_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 4 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_0 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 1 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_1 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 2 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_2 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 3 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_3 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 4 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25_4_4 :
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 5 5 (a+1) (c+1) degreeRows25_0 degreeP25 := by
  decide +kernel

lemma degreeCheck25 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows25_0.length, ∀ c ∈ List.range degreeRows25_0.length,
      residualCheck 25 6 2 (d+1) (e+1) (a+1) (c+1) degreeRows25_0 degreeP25 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck25_0_0
  · exact degreeCheck25_0_1
  · exact degreeCheck25_0_2
  · exact degreeCheck25_0_3
  · exact degreeCheck25_0_4
  · exact degreeCheck25_1_0
  · exact degreeCheck25_1_1
  · exact degreeCheck25_1_2
  · exact degreeCheck25_1_3
  · exact degreeCheck25_1_4
  · exact degreeCheck25_2_0
  · exact degreeCheck25_2_1
  · exact degreeCheck25_2_2
  · exact degreeCheck25_2_3
  · exact degreeCheck25_2_4
  · exact degreeCheck25_3_0
  · exact degreeCheck25_3_1
  · exact degreeCheck25_3_2
  · exact degreeCheck25_3_3
  · exact degreeCheck25_3_4
  · exact degreeCheck25_4_0
  · exact degreeCheck25_4_1
  · exact degreeCheck25_4_2
  · exact degreeCheck25_4_3
  · exact degreeCheck25_4_4

lemma degree_pos25 (μ : YoungDiagram) (hμ : μ.card = 25) :
    0 < kronecker (canonicalTableau (candidate 6 1 0) degreeCard25)
      (canonicalTableau (candidate 6 1 0) degreeCard25) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard25 degreeRows25_0 (by decide) (by decide)
    degreePlan25_0 (by decide) (by decide) (by decide) (by decide) degreeP25 ?_
    degreeCheck25 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard25 rfl degreeCones25
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
