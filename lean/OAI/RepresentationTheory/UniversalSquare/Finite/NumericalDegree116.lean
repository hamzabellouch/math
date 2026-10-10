import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks116
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof116

namespace OAI

/-! Numerical Degree 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos116 (μ : YoungDiagram) (hμ : μ.card = 116) :
    0 < kronecker (canonicalTableau (candidate 12 9 1) degreeCard116)
      (canonicalTableau (candidate 12 9 1) degreeCard116) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 19) (by decide) (by decide) rfl (by decide)
    degreeCard116 degreeRows116_0 (by decide) (by decide)
    degreePlan116_0 (by decide) (by decide) (by decide) (by decide) degreeP116 ?_
    degreeCheck116 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard116 rfl degreeCones116
    degreeTreeAll116 hr hn hh

end UniversalTensorSquare
end
end

end OAI
