import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData35

namespace OAI

/-! Degree Plans 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard35 : (candidate 6 3 1).card = 35 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan35_0 : PackingPlan := (.join (.twoPaths 8 [5,5,5,5]) (.join (.repeated 1 4) (.twosOdd 4 3 [6,5])))
def degreeRows35_0 : List ℕ := [6,5,5,5,5,5,4]

lemma degreeCone35_0 (μ : YoungDiagram) (hμ : μ.card = 35)
    (hd : RowsDom μ.rowLens degreeRows35_0) : SquareOccurs (candidate 6 3 1) μ := by
  exact candidate_cone (by decide) degreeCard35 degreePlan35_0 degreeRows35_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan35_1 : PackingPlan := (.join (.twoPaths 8 [5,5,5,5]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 4 2)))
def degreeRows35_1 : List ℕ := [8,5,5,5,5,2,2,2,1]

lemma degreeCone35_1 (μ : YoungDiagram) (hμ : μ.card = 35)
    (hd : RowsDom μ.rowLens degreeRows35_1) : SquareOccurs (candidate 6 3 1) μ := by
  exact candidate_cone (by decide) degreeCard35 degreePlan35_1 degreeRows35_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs35 : List (List ℕ) := [degreeRows35_1]

lemma degreeCones35 : ∀ q ∈ degreeQs35, ∀ μ : YoungDiagram, μ.card = 35 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 3 1) μ := by
  intro q hq
  simp only [degreeQs35,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone35_1

abbrev degreeP35 := TreeResidual 6 7 degreeQs35 degreeTree35

end UniversalTensorSquare
end
end

end OAI
