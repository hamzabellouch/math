import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks24
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof24

namespace OAI

/-! Numerical Degree 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos24 (μ : YoungDiagram) (hμ : μ.card = 24) :
    0 < kronecker (canonicalTableau (candidate 4 3 1) degreeCard24)
      (canonicalTableau (candidate 4 3 1) degreeCard24) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 7) (by decide) (by decide) rfl (by decide)
    degreeCard24 degreeRows24_0 (by decide) (by decide)
    degreePlan24_0 (by decide) (by decide) (by decide) (by decide) degreeP24 ?_
    degreeCheck24 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard24 rfl degreeCones24
    degreeTreeAll24 hr hn hh

end UniversalTensorSquare
end
end

end OAI
