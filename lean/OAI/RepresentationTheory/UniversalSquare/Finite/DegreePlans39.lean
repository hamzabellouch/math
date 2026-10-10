import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData39

namespace OAI

/-! Degree Plans 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard39 : (candidate 6 4 1).card = 39 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan39_0 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.repeated 1 4) (.twosOdd 5 3 [7,6])))
def degreeRows39_0 : List ℕ := [7,6,6,6,5,5,4]

lemma degreeCone39_0 (μ : YoungDiagram) (hμ : μ.card = 39)
    (hd : RowsDom μ.rowLens degreeRows39_0) : SquareOccurs (candidate 6 4 1) μ := by
  exact candidate_cone (by decide) degreeCard39 degreePlan39_0 degreeRows39_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan39_1 : PackingPlan := (.join (.twoPaths 9 [6,6,5,5]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 5 2)))
def degreeRows39_1 : List ℕ := [10,6,6,5,5,2,2,2,1]

lemma degreeCone39_1 (μ : YoungDiagram) (hμ : μ.card = 39)
    (hd : RowsDom μ.rowLens degreeRows39_1) : SquareOccurs (candidate 6 4 1) μ := by
  exact candidate_cone (by decide) degreeCard39 degreePlan39_1 degreeRows39_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs39 : List (List ℕ) := [degreeRows39_1]

lemma degreeCones39 : ∀ q ∈ degreeQs39, ∀ μ : YoungDiagram, μ.card = 39 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 4 1) μ := by
  intro q hq
  simp only [degreeQs39,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone39_1

abbrev degreeP39 := TreeResidual 6 9 degreeQs39 degreeTree39

end UniversalTensorSquare
end
end

end OAI
