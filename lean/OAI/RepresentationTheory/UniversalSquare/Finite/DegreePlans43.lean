import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData43

namespace OAI

/-! Degree Plans 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard43 : (candidate 6 5 1).card = 43 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan43_0 : PackingPlan := (.join (.twoPaths 10 [6,6,6,6]) (.join (.repeated 1 4) (.twosOdd 6 3 [8,7])))
def degreeRows43_0 : List ℕ := [8,7,6,6,6,6,4]

lemma degreeCone43_0 (μ : YoungDiagram) (hμ : μ.card = 43)
    (hd : RowsDom μ.rowLens degreeRows43_0) : SquareOccurs (candidate 6 5 1) μ := by
  exact candidate_cone (by decide) degreeCard43 degreePlan43_0 degreeRows43_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan43_1 : PackingPlan := (.join (.twoPaths 10 [6,6,6,6]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 6 2)))
def degreeRows43_1 : List ℕ := [12,6,6,6,6,2,2,2,1]

lemma degreeCone43_1 (μ : YoungDiagram) (hμ : μ.card = 43)
    (hd : RowsDom μ.rowLens degreeRows43_1) : SquareOccurs (candidate 6 5 1) μ := by
  exact candidate_cone (by decide) degreeCard43 degreePlan43_1 degreeRows43_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs43 : List (List ℕ) := [degreeRows43_1]

lemma degreeCones43 : ∀ q ∈ degreeQs43, ∀ μ : YoungDiagram, μ.card = 43 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 5 1) μ := by
  intro q hq
  simp only [degreeQs43,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone43_1

abbrev degreeP43 := TreeResidual 6 11 degreeQs43 degreeTree43

end UniversalTensorSquare
end
end

end OAI
