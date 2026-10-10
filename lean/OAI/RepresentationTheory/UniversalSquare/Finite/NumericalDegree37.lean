import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks37
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof37

namespace OAI

/-! Numerical Degree 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos37 (μ : YoungDiagram) (hμ : μ.card = 37) :
    0 < kronecker (canonicalTableau (candidate 6 4 0) degreeCard37)
      (canonicalTableau (candidate 6 4 0) degreeCard37) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 8) (by decide) (by decide) rfl (by decide)
    degreeCard37 degreeRows37_0 (by decide) (by decide)
    degreePlan37_0 (by decide) (by decide) (by decide) (by decide) degreeP37 ?_
    degreeCheck37 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard37 rfl degreeCones37
    degreeTreeAll37 hr hn hh

end UniversalTensorSquare
end
end

end OAI
