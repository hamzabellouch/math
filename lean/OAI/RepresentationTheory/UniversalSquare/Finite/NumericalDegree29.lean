import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Numerical Degree 29. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard29 : (candidate 6 2 0).card = 29 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan29_0 : PackingPlan := (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 3 1 [4,3])))
def degreeRows29_0 : List ℕ := [4,4,4,4,3,3,2,2,2,1]

lemma degreeCone29_0 (μ : YoungDiagram) (hμ : μ.card = 29)
    (hd : RowsDom μ.rowLens degreeRows29_0) : SquareOccurs (candidate 6 2 0) μ := by
  exact candidate_cone (by decide) degreeCard29 degreePlan29_0 degreeRows29_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs29 : List (List ℕ) := []

lemma degreeCones29 : ∀ q ∈ degreeQs29, ∀ μ : YoungDiagram, μ.card = 29 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 2 0) μ := by
  intro q hq
  simp only [degreeQs29,List.not_mem_nil] at hq

abbrev degreeP29 := ResidualProperty 6 4 degreeQs29 []

lemma degreeCheck29_0_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_0_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_0_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_0_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_0_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 1 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_1_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 2 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_2_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 3 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_3_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 4 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_0 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 1 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_1 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 2 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_2 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 3 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_3 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 4 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29_4_4 :
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 5 5 (a+1) (c+1) degreeRows29_0 degreeP29 := by
  decide +kernel

lemma degreeCheck29 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows29_0.length, ∀ c ∈ List.range degreeRows29_0.length,
      residualCheck 29 6 4 (d+1) (e+1) (a+1) (c+1) degreeRows29_0 degreeP29 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck29_0_0
  · exact degreeCheck29_0_1
  · exact degreeCheck29_0_2
  · exact degreeCheck29_0_3
  · exact degreeCheck29_0_4
  · exact degreeCheck29_1_0
  · exact degreeCheck29_1_1
  · exact degreeCheck29_1_2
  · exact degreeCheck29_1_3
  · exact degreeCheck29_1_4
  · exact degreeCheck29_2_0
  · exact degreeCheck29_2_1
  · exact degreeCheck29_2_2
  · exact degreeCheck29_2_3
  · exact degreeCheck29_2_4
  · exact degreeCheck29_3_0
  · exact degreeCheck29_3_1
  · exact degreeCheck29_3_2
  · exact degreeCheck29_3_3
  · exact degreeCheck29_3_4
  · exact degreeCheck29_4_0
  · exact degreeCheck29_4_1
  · exact degreeCheck29_4_2
  · exact degreeCheck29_4_3
  · exact degreeCheck29_4_4

lemma degree_pos29 (μ : YoungDiagram) (hμ : μ.card = 29) :
    0 < kronecker (canonicalTableau (candidate 6 2 0) degreeCard29)
      (canonicalTableau (candidate 6 2 0) degreeCard29) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard29 degreeRows29_0 (by decide) (by decide)
    degreePlan29_0 (by decide) (by decide) (by decide) (by decide) degreeP29 ?_
    degreeCheck29 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard29 rfl degreeCones29
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
