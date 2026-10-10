import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 51. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard51 : (candidate 9 1 1).card = 51 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan51_0 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 6 [4,3,3,3]) (.join (.neighbor 4 [3,2,2,2]) (.join (.repeated 1 3) (.repeated 2 2)))))
def degreeRows51_0 : List ℕ := [6,6,5,5,4,4,3,3,3,3,3,2,2,2]

lemma degreeCone51_0 (μ : YoungDiagram) (hμ : μ.card = 51)
    (hd : RowsDom μ.rowLens degreeRows51_0) : SquareOccurs (candidate 9 1 1) μ := by
  exact candidate_cone (by decide) degreeCard51 degreePlan51_0 degreeRows51_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs51 : List (List ℕ) := []

lemma degreeCones51 : ∀ q ∈ degreeQs51, ∀ μ : YoungDiagram, μ.card = 51 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 9 1 1) μ := by
  intro q hq
  simp only [degreeQs51,List.not_mem_nil] at hq

abbrev degreeP51 := ResidualProperty 9 3 degreeQs51 []

lemma degreeCheck51_0_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_0_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_0_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_0_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_0_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 1 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_1_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 2 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_2_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 3 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_3_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 4 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_0 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 1 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_1 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 2 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_2 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 3 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_3 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 4 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51_4_4 :
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 5 5 (a+1) (c+1) degreeRows51_0 degreeP51 := by
  decide +kernel

lemma degreeCheck51 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows51_0.length, ∀ c ∈ List.range degreeRows51_0.length,
      residualCheck 51 9 3 (d+1) (e+1) (a+1) (c+1) degreeRows51_0 degreeP51 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck51_0_0
  · exact degreeCheck51_0_1
  · exact degreeCheck51_0_2
  · exact degreeCheck51_0_3
  · exact degreeCheck51_0_4
  · exact degreeCheck51_1_0
  · exact degreeCheck51_1_1
  · exact degreeCheck51_1_2
  · exact degreeCheck51_1_3
  · exact degreeCheck51_1_4
  · exact degreeCheck51_2_0
  · exact degreeCheck51_2_1
  · exact degreeCheck51_2_2
  · exact degreeCheck51_2_3
  · exact degreeCheck51_2_4
  · exact degreeCheck51_3_0
  · exact degreeCheck51_3_1
  · exact degreeCheck51_3_2
  · exact degreeCheck51_3_3
  · exact degreeCheck51_3_4
  · exact degreeCheck51_4_0
  · exact degreeCheck51_4_1
  · exact degreeCheck51_4_2
  · exact degreeCheck51_4_3
  · exact degreeCheck51_4_4

lemma degree_pos51 (μ : YoungDiagram) (hμ : μ.card = 51) :
    0 < kronecker (canonicalTableau (candidate 9 1 1) degreeCard51)
      (canonicalTableau (candidate 9 1 1) degreeCard51) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 3) (by decide) (by decide) rfl (by decide)
    degreeCard51 degreeRows51_0 (by decide) (by decide)
    degreePlan51_0 (by decide) (by decide) (by decide) (by decide) degreeP51 ?_
    degreeCheck51 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard51 rfl degreeCones51
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
