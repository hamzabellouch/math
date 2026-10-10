import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData41

namespace OAI

/-! Degree Plans 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard41 : (candidate 6 5 0).card = 41 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan41_0 : PackingPlan := (.join (.neighbor 10 [6,5,5,5]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 6 1 [7,6])))
def degreeRows41_0 : List ℕ := [7,6,6,5,5,5,2,2,2,1]

lemma degreeCone41_0 (μ : YoungDiagram) (hμ : μ.card = 41)
    (hd : RowsDom μ.rowLens degreeRows41_0) : SquareOccurs (candidate 6 5 0) μ := by
  exact candidate_cone (by decide) degreeCard41 degreePlan41_0 degreeRows41_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs41 : List (List ℕ) := []

lemma degreeCones41 : ∀ q ∈ degreeQs41, ∀ μ : YoungDiagram, μ.card = 41 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 5 0) μ := by
  intro q hq
  simp only [degreeQs41,List.not_mem_nil] at hq

abbrev degreeP41 := TreeResidual 6 10 degreeQs41 degreeTree41

end UniversalTensorSquare
end
end

end OAI
