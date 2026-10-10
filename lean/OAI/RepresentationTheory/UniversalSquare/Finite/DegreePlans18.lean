import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData18

namespace OAI

/-! Degree Plans 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard18 : (candidate 4 2 0).card = 18 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan18_0 : PackingPlan := (.join (.neighbor 5 [3,3,3,2]) (.twosOdd 3 1 [4,3]))
def degreeRows18_0 : List ℕ := [4,3,3,3,3,2]

lemma degreeCone18_0 (μ : YoungDiagram) (hμ : μ.card = 18)
    (hd : RowsDom μ.rowLens degreeRows18_0) : SquareOccurs (candidate 4 2 0) μ := by
  exact candidate_cone (by decide) degreeCard18 degreePlan18_0 degreeRows18_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs18 : List (List ℕ) := []

lemma degreeCones18 : ∀ q ∈ degreeQs18, ∀ μ : YoungDiagram, μ.card = 18 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 2 0) μ := by
  intro q hq
  simp only [degreeQs18,List.not_mem_nil] at hq

abbrev degreeP18 := TreeResidual 4 4 degreeQs18 degreeTree18

end UniversalTensorSquare
end
end

end OAI
