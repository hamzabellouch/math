import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData24

namespace OAI

/-! Degree Plans 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard24 : (candidate 4 3 1).card = 24 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan24_0 : PackingPlan := (.join (.twoPaths 6 [4,4,4,4]) (.repeated 4 2))
def degreeRows24_0 : List ℕ := [8,4,4,4,4]

lemma degreeCone24_0 (μ : YoungDiagram) (hμ : μ.card = 24)
    (hd : RowsDom μ.rowLens degreeRows24_0) : SquareOccurs (candidate 4 3 1) μ := by
  exact candidate_cone (by decide) degreeCard24 degreePlan24_0 degreeRows24_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs24 : List (List ℕ) := []

lemma degreeCones24 : ∀ q ∈ degreeQs24, ∀ μ : YoungDiagram, μ.card = 24 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 3 1) μ := by
  intro q hq
  simp only [degreeQs24,List.not_mem_nil] at hq

abbrev degreeP24 := TreeResidual 4 7 degreeQs24 degreeTree24

end UniversalTensorSquare
end
end

end OAI
