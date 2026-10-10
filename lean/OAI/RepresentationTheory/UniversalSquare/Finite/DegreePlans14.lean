import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData14

namespace OAI

/-! Degree Plans 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard14 : (candidate 4 1 0).card = 14 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan14_0 : PackingPlan := (.join (.neighbor 4 [3,2,2,2]) (.twosOdd 2 1 [3,2]))
def degreeRows14_0 : List ℕ := [3,3,2,2,2,2]

lemma degreeCone14_0 (μ : YoungDiagram) (hμ : μ.card = 14)
    (hd : RowsDom μ.rowLens degreeRows14_0) : SquareOccurs (candidate 4 1 0) μ := by
  exact candidate_cone (by decide) degreeCard14 degreePlan14_0 degreeRows14_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs14 : List (List ℕ) := []

lemma degreeCones14 : ∀ q ∈ degreeQs14, ∀ μ : YoungDiagram, μ.card = 14 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 1 0) μ := by
  intro q hq
  simp only [degreeQs14,List.not_mem_nil] at hq

abbrev degreeP14 := TreeResidual 4 2 degreeQs14 degreeTree14

end UniversalTensorSquare
end
end

end OAI
