import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData22

namespace OAI

/-! Degree Plans 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard22 : (candidate 4 3 0).card = 22 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan22_0 : PackingPlan := (.join (.neighbor 6 [4,3,3,3]) (.twosOdd 4 1 [5,4]))
def degreeRows22_0 : List ℕ := [5,4,4,3,3,3]

lemma degreeCone22_0 (μ : YoungDiagram) (hμ : μ.card = 22)
    (hd : RowsDom μ.rowLens degreeRows22_0) : SquareOccurs (candidate 4 3 0) μ := by
  exact candidate_cone (by decide) degreeCard22 degreePlan22_0 degreeRows22_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs22 : List (List ℕ) := []

lemma degreeCones22 : ∀ q ∈ degreeQs22, ∀ μ : YoungDiagram, μ.card = 22 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 3 0) μ := by
  intro q hq
  simp only [degreeQs22,List.not_mem_nil] at hq

abbrev degreeP22 := TreeResidual 4 6 degreeQs22 degreeTree22

end UniversalTensorSquare
end
end

end OAI
