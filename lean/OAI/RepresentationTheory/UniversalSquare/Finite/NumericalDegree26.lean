import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks26
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof26

namespace OAI

/-! Numerical Degree 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos26 (μ : YoungDiagram) (hμ : μ.card = 26) :
    0 < kronecker (canonicalTableau (candidate 4 4 0) degreeCard26)
      (canonicalTableau (candidate 4 4 0) degreeCard26) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 8) (by decide) (by decide) rfl (by decide)
    degreeCard26 degreeRows26_0 (by decide) (by decide)
    degreePlan26_0 (by decide) (by decide) (by decide) (by decide) degreeP26 ?_
    degreeCheck26 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard26 rfl degreeCones26
    degreeTreeAll26 hr hn hh

end UniversalTensorSquare
end
end

end OAI
