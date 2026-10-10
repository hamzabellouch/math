import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData37

namespace OAI

/-! Degree Plans 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard37 : (candidate 6 4 0).card = 37 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan37_0 : PackingPlan := (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 5 1 [6,5])))
def degreeRows37_0 : List ℕ := [6,5,5,5,5,4,2,2,2,1]

lemma degreeCone37_0 (μ : YoungDiagram) (hμ : μ.card = 37)
    (hd : RowsDom μ.rowLens degreeRows37_0) : SquareOccurs (candidate 6 4 0) μ := by
  exact candidate_cone (by decide) degreeCard37 degreePlan37_0 degreeRows37_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs37 : List (List ℕ) := []

lemma degreeCones37 : ∀ q ∈ degreeQs37, ∀ μ : YoungDiagram, μ.card = 37 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 4 0) μ := by
  intro q hq
  simp only [degreeQs37, List.not_mem_nil] at hq

abbrev degreeP37 := TreeResidual 6 8 degreeQs37 degreeTree37

end UniversalTensorSquare
end
end

end OAI
