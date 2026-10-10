import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks31
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof31

namespace OAI

/-! Numerical Degree 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos31 (μ : YoungDiagram) (hμ : μ.card = 31) :
    0 < kronecker (canonicalTableau (candidate 6 2 1) degreeCard31)
      (canonicalTableau (candidate 6 2 1) degreeCard31) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 5) (by decide) (by decide) rfl (by decide)
    degreeCard31 degreeRows31_0 (by decide) (by decide)
    degreePlan31_0 (by decide) (by decide) (by decide) (by decide) degreeP31 ?_
    degreeCheck31 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard31 rfl degreeCones31
    degreeTreeAll31 hr hn hh

end UniversalTensorSquare
end
end

end OAI
