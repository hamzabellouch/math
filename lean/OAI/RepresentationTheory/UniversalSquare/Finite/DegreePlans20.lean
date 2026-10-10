import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData20

namespace OAI

/-! Degree Plans 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard20 : (candidate 4 2 1).card = 20 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan20_0 : PackingPlan := (.join (.twoPaths 5 [4,4,3,3]) (.repeated 3 2))
def degreeRows20_0 : List ℕ := [6,4,4,3,3]

lemma degreeCone20_0 (μ : YoungDiagram) (hμ : μ.card = 20)
    (hd : RowsDom μ.rowLens degreeRows20_0) : SquareOccurs (candidate 4 2 1) μ := by
  exact candidate_cone (by decide) degreeCard20 degreePlan20_0 degreeRows20_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs20 : List (List ℕ) := []

lemma degreeCones20 : ∀ q ∈ degreeQs20, ∀ μ : YoungDiagram, μ.card = 20 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 2 1) μ := by
  intro q hq
  simp only [degreeQs20,List.not_mem_nil] at hq

abbrev degreeP20 := TreeResidual 4 5 degreeQs20 degreeTree20

end UniversalTensorSquare
end
end

end OAI
