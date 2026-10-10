import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks89
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof89

namespace OAI

/-! Numerical Degree 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos89 (μ : YoungDiagram) (hμ : μ.card = 89) :
    0 < kronecker (canonicalTableau (candidate 10 8 1) degreeCard89)
      (canonicalTableau (candidate 10 8 1) degreeCard89) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 17) (by decide) (by decide) rfl (by decide)
    degreeCard89 degreeRows89_0 (by decide) (by decide)
    degreePlan89_0 (by decide) (by decide) (by decide) (by decide) degreeP89 ?_
    degreeCheck89 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard89 rfl degreeCones89
    degreeTreeAll89 hr hn hh

end UniversalTensorSquare
end
end

end OAI
