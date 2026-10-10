import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData64

namespace OAI

/-! Degree Plans 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard64 : (candidate 8 7 0).card = 64 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan64_0 : PackingPlan := (.join (.neighbor 14 [8,7,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 8 1 [9,8]))))
def degreeRows64_0 : List ℕ := [9,8,8,7,7,7,3,3,3,2,2,2,2,1]

lemma degreeCone64_0 (μ : YoungDiagram) (hμ : μ.card = 64)
    (hd : RowsDom μ.rowLens degreeRows64_0) : SquareOccurs (candidate 8 7 0) μ := by
  exact candidate_cone (by decide) degreeCard64 degreePlan64_0 degreeRows64_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs64 : List (List ℕ) := []

lemma degreeCones64 : ∀ q ∈ degreeQs64, ∀ μ : YoungDiagram, μ.card = 64 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 7 0) μ := by
  intro q hq
  simp only [degreeQs64, List.not_mem_nil] at hq

abbrev degreeP64 := TreeResidual 8 14 degreeQs64 degreeTree64

end UniversalTensorSquare
end
end

end OAI
