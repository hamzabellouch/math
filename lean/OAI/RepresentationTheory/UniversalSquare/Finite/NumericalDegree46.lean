import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard46 : (candidate 8 2 1).card = 46 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan46_0 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 3 3 [5,4]))))
def degreeRows46_0 : List ℕ := [6,6,5,5,5,4,4,3,3,3,2]

lemma degreeCone46_0 (μ : YoungDiagram) (hμ : μ.card = 46)
    (hd : RowsDom μ.rowLens degreeRows46_0) : SquareOccurs (candidate 8 2 1) μ := by
  exact candidate_cone (by decide) degreeCard46 degreePlan46_0 degreeRows46_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan46_1 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 3 2))))
def degreeRows46_1 : List ℕ := [6,6,6,5,5,3,3,3,2,2,2,2,1]

lemma degreeCone46_1 (μ : YoungDiagram) (hμ : μ.card = 46)
    (hd : RowsDom μ.rowLens degreeRows46_1) : SquareOccurs (candidate 8 2 1) μ := by
  exact candidate_cone (by decide) degreeCard46 degreePlan46_1 degreeRows46_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs46 : List (List ℕ) := [degreeRows46_1]

lemma degreeCones46 : ∀ q ∈ degreeQs46, ∀ μ : YoungDiagram, μ.card = 46 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 2 1) μ := by
  intro q hq
  simp only [degreeQs46,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone46_1

abbrev degreeP46 := ResidualProperty 8 5 degreeQs46 []

lemma degreeCheck46_0_0 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 1 1 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_0_1 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 1 2 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_0_2 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 1 3 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_0_3 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 1 4 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_0_4 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 1 5 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_1_0 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 2 1 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_1_1 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 2 2 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_1_2 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 2 3 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_1_3 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 2 4 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_1_4 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 2 5 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_2_0 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 3 1 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_2_1 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 3 2 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_2_2 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 3 3 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_2_3 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 3 4 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_2_4 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 3 5 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_3_0 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 4 1 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_3_1 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 4 2 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_3_2 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 4 3 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_3_3 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 4 4 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_3_4 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 4 5 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_4_0 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 5 1 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_4_1 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 5 2 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_4_2 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 5 3 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_4_3 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 5 4 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46_4_4 :
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 5 5 (a+1) (c+1) degreeRows46_0 degreeP46 := by
  decide +kernel

lemma degreeCheck46 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows46_0.length, ∀ c ∈ List.range degreeRows46_0.length,
      residualCheck 46 8 5 (d+1) (e+1) (a+1) (c+1) degreeRows46_0 degreeP46 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck46_0_0
  · exact degreeCheck46_0_1
  · exact degreeCheck46_0_2
  · exact degreeCheck46_0_3
  · exact degreeCheck46_0_4
  · exact degreeCheck46_1_0
  · exact degreeCheck46_1_1
  · exact degreeCheck46_1_2
  · exact degreeCheck46_1_3
  · exact degreeCheck46_1_4
  · exact degreeCheck46_2_0
  · exact degreeCheck46_2_1
  · exact degreeCheck46_2_2
  · exact degreeCheck46_2_3
  · exact degreeCheck46_2_4
  · exact degreeCheck46_3_0
  · exact degreeCheck46_3_1
  · exact degreeCheck46_3_2
  · exact degreeCheck46_3_3
  · exact degreeCheck46_3_4
  · exact degreeCheck46_4_0
  · exact degreeCheck46_4_1
  · exact degreeCheck46_4_2
  · exact degreeCheck46_4_3
  · exact degreeCheck46_4_4

lemma degree_pos46 (μ : YoungDiagram) (hμ : μ.card = 46) :
    0 < kronecker (canonicalTableau (candidate 8 2 1) degreeCard46)
      (canonicalTableau (candidate 8 2 1) degreeCard46) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 5) (by decide) (by decide) rfl (by decide)
    degreeCard46 degreeRows46_0 (by decide) (by decide)
    degreePlan46_0 (by decide) (by decide) (by decide) (by decide) degreeP46 ?_
    degreeCheck46 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard46 rfl degreeCones46
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
