import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData62

namespace OAI

/-! Degree Plans 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard62 : (candidate 8 6 1).card = 62 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan62_0 : PackingPlan := (.join (.twoPaths 13 [8,8,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 7 3 [9,8]))))
def degreeRows62_0 : List ℕ := [9,8,8,8,7,7,4,3,3,3,2]

lemma degreeCone62_0 (μ : YoungDiagram) (hμ : μ.card = 62)
    (hd : RowsDom μ.rowLens degreeRows62_0) : SquareOccurs (candidate 8 6 1) μ := by
  exact candidate_cone (by decide) degreeCard62 degreePlan62_0 degreeRows62_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan62_1 : PackingPlan := (.join (.twoPaths 13 [8,8,7,7]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 7 2))))
def degreeRows62_1 : List ℕ := [14,8,8,7,7,3,3,3,2,2,2,2,1]

lemma degreeCone62_1 (μ : YoungDiagram) (hμ : μ.card = 62)
    (hd : RowsDom μ.rowLens degreeRows62_1) : SquareOccurs (candidate 8 6 1) μ := by
  exact candidate_cone (by decide) degreeCard62 degreePlan62_1 degreeRows62_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs62 : List (List ℕ) := [degreeRows62_1]

lemma degreeCones62 : ∀ q ∈ degreeQs62, ∀ μ : YoungDiagram, μ.card = 62 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 8 6 1) μ := by
  intro q hq
  simp only [degreeQs62,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone62_1

abbrev degreeP62 := TreeResidual 8 13 degreeQs62 degreeTree62

end UniversalTensorSquare
end
end

end OAI
