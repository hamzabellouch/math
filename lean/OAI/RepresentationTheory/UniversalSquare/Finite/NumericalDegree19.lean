import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks19
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof19

namespace OAI

/-! Numerical Degree 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos19 (μ : YoungDiagram) (hμ : μ.card = 19) :
    0 < kronecker (canonicalTableau (candidate 5 1 0) degreeCard19)
      (canonicalTableau (candidate 5 1 0) degreeCard19) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard19 degreeRows19_0 (by decide) (by decide)
    degreePlan19_0 (by decide) (by decide) (by decide) (by decide) degreeP19 ?_
    degreeCheck19 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard19 rfl degreeCones19
    degreeTreeAll19 hr hn hh

end UniversalTensorSquare
end
end

end OAI
