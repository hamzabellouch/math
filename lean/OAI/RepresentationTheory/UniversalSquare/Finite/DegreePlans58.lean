import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData58

namespace OAI

/-! Degree Plans 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard58 : (candidate 8 5 1).card = 58 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan58_0 : PackingPlan := (.join (.twoPaths 12 [7,7,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 6 3 [8,7]))))
def degreeRows58_0 : List ℕ := [8,7,7,7,7,7,4,3,3,3,2]

lemma degreeCone58_0 (μ : YoungDiagram) (hμ : μ.card = 58)
    (hd : RowsDom μ.rowLens degreeRows58_0) : SquareOccurs (candidate 8 5 1) μ := by
  exact candidate_cone (by decide) degreeCard58 degreePlan58_0 degreeRows58_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan58_1 : PackingPlan := (.join (.twoPaths 12 [7,7,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 6 2))))
def degreeRows58_1 : List ℕ := [12,7,7,7,7,3,3,3,2,2,2,2,1]

lemma degreeCone58_1 (μ : YoungDiagram) (hμ : μ.card = 58)
    (hd : RowsDom μ.rowLens degreeRows58_1) : SquareOccurs (candidate 8 5 1) μ := by
  exact candidate_cone (by decide) degreeCard58 degreePlan58_1 degreeRows58_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs58 : List (List ℕ) := [degreeRows58_1]

lemma degreeCones58 : ∀ q ∈ degreeQs58, ∀ μ : YoungDiagram, μ.card = 58 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 5 1) μ := by
  intro q hq
  simp only [degreeQs58,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone58_1

abbrev degreeP58 := TreeResidual 8 11 degreeQs58 degreeTree58

end UniversalTensorSquare
end
end

end OAI
