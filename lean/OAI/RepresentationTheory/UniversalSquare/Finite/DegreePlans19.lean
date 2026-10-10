import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData19

namespace OAI

/-! Degree Plans 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard19 : (candidate 5 1 0).card = 19 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan19_0 : PackingPlan := (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 3) (.twosOdd 2 1 [3,2])))
def degreeRows19_0 : List ℕ := [3,3,3,3,3,2,2]

lemma degreeCone19_0 (μ : YoungDiagram) (hμ : μ.card = 19)
    (hd : RowsDom μ.rowLens degreeRows19_0) : SquareOccurs (candidate 5 1 0) μ := by
  exact candidate_cone (by decide) degreeCard19 degreePlan19_0 degreeRows19_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs19 : List (List ℕ) := []

lemma degreeCones19 : ∀ q ∈ degreeQs19, ∀ μ : YoungDiagram, μ.card = 19 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 5 1 0) μ := by
  intro q hq
  simp only [degreeQs19, List.not_mem_nil] at hq

abbrev degreeP19 := TreeResidual 5 2 degreeQs19 degreeTree19

end UniversalTensorSquare
end
end

end OAI
