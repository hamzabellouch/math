import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData26

namespace OAI

/-! Degree Plans 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard26 : (candidate 4 4 0).card = 26 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan26_0 : PackingPlan := (.join (.neighbor 7 [4,4,4,3]) (.twosOdd 5 1 [6,5]))
def degreeRows26_0 : List ℕ := [6,5,4,4,4,3]

lemma degreeCone26_0 (μ : YoungDiagram) (hμ : μ.card = 26)
    (hd : RowsDom μ.rowLens degreeRows26_0) : SquareOccurs (candidate 4 4 0) μ := by
  exact candidate_cone (by decide) degreeCard26 degreePlan26_0 degreeRows26_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs26 : List (List ℕ) := []

lemma degreeCones26 : ∀ q ∈ degreeQs26, ∀ μ : YoungDiagram, μ.card = 26 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 4 0) μ := by
  intro q hq
  simp only [degreeQs26,List.not_mem_nil] at hq

abbrev degreeP26 := TreeResidual 4 8 degreeQs26 degreeTree26

end UniversalTensorSquare
end
end

end OAI
