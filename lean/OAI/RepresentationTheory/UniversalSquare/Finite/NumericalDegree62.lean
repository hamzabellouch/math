import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks62
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof62

namespace OAI

/-! Numerical Degree 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos62 (μ : YoungDiagram) (hμ : μ.card = 62) :
    0 < kronecker (canonicalTableau (candidate 8 6 1) degreeCard62)
      (canonicalTableau (candidate 8 6 1) degreeCard62) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 13) (by decide) (by decide) rfl (by decide)
    degreeCard62 degreeRows62_0 (by decide) (by decide)
    degreePlan62_0 (by decide) (by decide) (by decide) (by decide) degreeP62 ?_
    degreeCheck62 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard62 rfl degreeCones62
    degreeTreeAll62 hr hn hh

end UniversalTensorSquare
end
end

end OAI
