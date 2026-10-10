import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData16

namespace OAI

/-! Degree Plans 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCard16 : (candidate 4 1 1).card = 16 := by
  rw [candidate_card _ _ _ (by decide), staircase_card]

def degreePlan16_0 : PackingPlan := (.join (.twoPaths 4 [3,3,3,3]) (.repeated 2 2))
def degreeRows16_0 : List ℕ := [4,3,3,3,3]

lemma degreeCone16_0 (μ : YoungDiagram) (hμ : μ.card = 16)
    (hd : RowsDom μ.rowLens degreeRows16_0) : SquareOccurs (candidate 4 1 1) μ := by
  exact candidate_cone (by decide) degreeCard16 degreePlan16_0 degreeRows16_0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) μ hμ hd

def degreeQs16 : List (List ℕ) := []

lemma degreeCones16 : ∀ q ∈ degreeQs16, ∀ μ : YoungDiagram, μ.card = 16 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 1 1) μ := by
  intro q hq
  simp only [degreeQs16, List.not_mem_nil] at hq

abbrev degreeP16 := TreeResidual 4 3 degreeQs16 degreeTree16

end UniversalTensorSquare
end
end

end OAI
