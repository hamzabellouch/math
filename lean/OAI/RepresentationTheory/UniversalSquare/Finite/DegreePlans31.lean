import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData31

namespace OAI

/-! Degree Plans 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard31 : (candidate 6 2 1).card = 31 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan31_0 : PackingPlan := (.join (.twoPaths 7 [5,5,4,4]) (.join (.repeated 1 4) (.twosOdd 3 3 [5,4])))
def degreeRows31_0 : List ℕ := [5,5,5,4,4,4,4]

lemma degreeCone31_0 (μ : YoungDiagram) (hμ : μ.card = 31)
    (hd : RowsDom μ.rowLens degreeRows31_0) : SquareOccurs (candidate 6 2 1) μ := by
  exact candidate_cone (by decide) degreeCard31 degreePlan31_0 degreeRows31_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreePlan31_1 : PackingPlan := (.join (.twoPaths 7 [5,5,4,4]) (.join (.neighbor 3 [2,2,2,1]) (.repeated 3 2)))
def degreeRows31_1 : List ℕ := [6,5,5,4,4,2,2,2,1]

lemma degreeCone31_1 (μ : YoungDiagram) (hμ : μ.card = 31)
    (hd : RowsDom μ.rowLens degreeRows31_1) : SquareOccurs (candidate 6 2 1) μ := by
  exact candidate_cone (by decide) degreeCard31 degreePlan31_1 degreeRows31_1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs31 : List (List ℕ) := [degreeRows31_1]

lemma degreeCones31 : ∀ q ∈ degreeQs31, ∀ μ : YoungDiagram, μ.card = 31 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 6 2 1) μ := by
  intro q hq
  simp only [degreeQs31,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · exact degreeCone31_1

abbrev degreeP31 := TreeResidual 6 5 degreeQs31 degreeTree31

end UniversalTensorSquare
end
end

end OAI
