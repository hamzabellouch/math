import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData89

namespace OAI

/-! Degree Plans 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard89 : (candidate 10 8 1).card = 89 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan89_0 : PackingPlan := (.join (.twoPaths 17 [10,10,9,9]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 9 3 [11,10])))))
def degreeRows89_0 : List ℕ := [11,10,10,10,9,9,4,4,4,4,3,3,3,3,2]

lemma degreeCone89_0 (μ : YoungDiagram) (hμ : μ.card = 89)
    (hd : RowsDom μ.rowLens degreeRows89_0) : SquareOccurs (candidate 10 8 1) μ := by
  exact candidate_cone (by decide) degreeCard89 degreePlan89_0 degreeRows89_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan89_1 : PackingPlan := (.join (.twoPaths 17 [10,10,9,9]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 9 2)))))
def degreeRows89_1 : List ℕ := [18,10,10,9,9,4,4,4,3,3,3,3,2,2,2,2,1]

lemma degreeCone89_1 (μ : YoungDiagram) (hμ : μ.card = 89)
    (hd : RowsDom μ.rowLens degreeRows89_1) : SquareOccurs (candidate 10 8 1) μ := by
  exact candidate_cone (by decide) degreeCard89 degreePlan89_1 degreeRows89_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs89 : List (List ℕ) := [degreeRows89_1]

lemma degreeCones89 : ∀ q ∈ degreeQs89, ∀ μ : YoungDiagram, μ.card = 89 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 10 8 1) μ := by
  intro q hq
  simp only [degreeQs89,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone89_1

abbrev degreeP89 := TreeResidual 10 17 degreeQs89 degreeTree89

end UniversalTensorSquare
end
end

end OAI
