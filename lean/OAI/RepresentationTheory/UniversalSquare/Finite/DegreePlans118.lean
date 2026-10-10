import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData118

namespace OAI

/-! Degree Plans 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard118 : (candidate 12 10 0).card = 118 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan118_0 : PackingPlan := (.join (.neighbor 21 [11,11,11,10]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.twosOdd 11 1 [12,11]))))))
def degreeRows118_0 : List ℕ := [12,11,11,11,11,10,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

lemma degreeCone118_0 (μ : YoungDiagram) (hμ : μ.card = 118)
    (hd : RowsDom μ.rowLens degreeRows118_0) : SquareOccurs (candidate 12 10 0) μ := by
  exact candidate_cone (by decide) degreeCard118 degreePlan118_0 degreeRows118_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs118 : List (List ℕ) := []

lemma degreeCones118 : ∀ q ∈ degreeQs118, ∀ μ : YoungDiagram, μ.card = 118 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 12 10 0) μ := by
  intro q hq
  simp only [degreeQs118,List.not_mem_nil] at hq

abbrev degreeP118 := TreeResidual 12 20 degreeQs118 degreeTree118

end UniversalTensorSquare
end
end

end OAI
