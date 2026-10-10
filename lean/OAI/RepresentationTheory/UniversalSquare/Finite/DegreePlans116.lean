import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData116

namespace OAI

/-! Degree Plans 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard116 : (candidate 12 9 1).card = 116 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan116_0 : PackingPlan := (.join (.twoPaths 20 [11,11,11,11]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.repeated 1 4) (.twosOdd 10 3 [12,11]))))))
def degreeRows116_0 : List ℕ := [12,11,11,11,11,11,5,5,5,4,4,4,4,4,3,3,3,3,2]

lemma degreeCone116_0 (μ : YoungDiagram) (hμ : μ.card = 116)
    (hd : RowsDom μ.rowLens degreeRows116_0) : SquareOccurs (candidate 12 9 1) μ := by
  exact candidate_cone (by decide) degreeCard116 degreePlan116_0 degreeRows116_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan116_1 : PackingPlan := (.join (.twoPaths 20 [11,11,11,11]) (.join (.neighbor 9 [5,5,5,4]) (.join (.neighbor 7 [4,4,4,3]) (.join (.neighbor 5 [3,3,3,2]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 10 2))))))
def degreeRows116_1 : List ℕ := [20,11,11,11,11,5,5,5,4,4,4,4,3,3,3,3,2,2,2,2,1]

lemma degreeCone116_1 (μ : YoungDiagram) (hμ : μ.card = 116)
    (hd : RowsDom μ.rowLens degreeRows116_1) : SquareOccurs (candidate 12 9 1) μ := by
  exact candidate_cone (by decide) degreeCard116 degreePlan116_1 degreeRows116_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs116 : List (List ℕ) := [degreeRows116_1]

lemma degreeCones116 : ∀ q ∈ degreeQs116, ∀ μ : YoungDiagram, μ.card = 116 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 12 9 1) μ := by
  intro q hq
  simp only [degreeQs116,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone116_1

abbrev degreeP116 := TreeResidual 12 19 degreeQs116 degreeTree116

end UniversalTensorSquare
end
end

end OAI
