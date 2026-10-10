import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.RowSquareTools

namespace OAI

/-! Numerical Degree 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard12 : (candidate 4 0 1).card = 12 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan12_0 : PackingPlan := (.join (.twoPaths 3 [3,3,2,2]) (.repeated 1 2))
def degreeRows12_0 : List ℕ := [3,3,2,2,2]

lemma degreeCone12_0 (μ : YoungDiagram) (hμ : μ.card = 12)
    (hd : RowsDom μ.rowLens degreeRows12_0) : SquareOccurs (candidate 4 0 1) μ := by
  exact candidate_cone (by decide) degreeCard12 degreePlan12_0 degreeRows12_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan12_1 : PackingPlan := (.join (.repeated 1 5) (.join (.neighbor 2 [2,1,1,1]) (.repeated 2 1)))
def degreeRows12_1 : List ℕ := [5,2,2,1,1,1]

lemma degreeCone12_1 (μ : YoungDiagram) (hμ : μ.card = 12)
    (hd : RowsDom μ.rowLens degreeRows12_1) : SquareOccurs (candidate 4 0 1) μ := by
  exact candidate_cone (by decide) degreeCard12 degreePlan12_1 degreeRows12_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs12 : List (List ℕ) := [degreeRows12_1]

lemma degreeCones12 : ∀ q ∈ degreeQs12, ∀ μ : YoungDiagram, μ.card = 12 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 0 1) μ := by
  intro q hq
  simp only [degreeQs12,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone12_1

abbrev degreeP12 := ResidualProperty 4 1 degreeQs12 []

lemma degreeCheck12_0_0 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 1 1 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_0_1 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 1 2 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_0_2 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 1 3 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_0_3 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 1 4 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_0_4 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 1 5 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_1_0 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 2 1 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_1_1 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 2 2 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_1_2 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 2 3 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_1_3 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 2 4 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_1_4 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 2 5 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_2_0 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 3 1 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_2_1 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 3 2 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_2_2 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 3 3 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_2_3 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 3 4 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_2_4 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 3 5 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_3_0 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 4 1 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_3_1 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 4 2 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_3_2 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 4 3 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_3_3 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 4 4 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_3_4 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 4 5 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_4_0 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 5 1 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_4_1 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 5 2 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_4_2 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 5 3 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_4_3 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 5 4 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12_4_4 :
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 5 5 (a+1) (c+1) degreeRows12_0 degreeP12 := by
  decide +kernel

lemma degreeCheck12 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows12_0.length, ∀ c ∈ List.range degreeRows12_0.length,
      residualCheck 12 4 1 (d+1) (e+1) (a+1) (c+1) degreeRows12_0 degreeP12 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCheck12_0_0
  · exact degreeCheck12_0_1
  · exact degreeCheck12_0_2
  · exact degreeCheck12_0_3
  · exact degreeCheck12_0_4
  · exact degreeCheck12_1_0
  · exact degreeCheck12_1_1
  · exact degreeCheck12_1_2
  · exact degreeCheck12_1_3
  · exact degreeCheck12_1_4
  · exact degreeCheck12_2_0
  · exact degreeCheck12_2_1
  · exact degreeCheck12_2_2
  · exact degreeCheck12_2_3
  · exact degreeCheck12_2_4
  · exact degreeCheck12_3_0
  · exact degreeCheck12_3_1
  · exact degreeCheck12_3_2
  · exact degreeCheck12_3_3
  · exact degreeCheck12_3_4
  · exact degreeCheck12_4_0
  · exact degreeCheck12_4_1
  · exact degreeCheck12_4_2
  · exact degreeCheck12_4_3
  · exact degreeCheck12_4_4

lemma degree_pos12 (μ : YoungDiagram) (hμ : μ.card = 12) :
    0 < kronecker (canonicalTableau (candidate 4 0 1) degreeCard12)
      (canonicalTableau (candidate 4 0 1) degreeCard12) (canonicalTableau μ hμ) := by
  apply candidate_residual_pos (r := 1) (by decide) (by decide) rfl (by decide)
    degreeCard12 degreeRows12_0 (by decide) (by decide)
    degreePlan12_0 (by decide) (by decide) (by decide) (by decide) degreeP12 ?_
    degreeCheck12 μ hμ
  intro rs hr hn hh
  exact residualProperty_sound (by decide) (by decide) degreeCard12 rfl degreeCones12
    (by simp) hr hn hh

end UniversalTensorSquare
end
end

end OAI
