import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks43
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof43

namespace OAI

/-! Numerical Degree 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos43 (μ : YoungDiagram) (hμ : μ.card = 43) :
    0 < kronecker (canonicalTableau (candidate 6 5 1) degreeCard43)
      (canonicalTableau (candidate 6 5 1) degreeCard43) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 11) (by decide) (by decide) rfl (by decide)
    degreeCard43 degreeRows43_0 (by decide) (by decide)
    degreePlan43_0 (by decide) (by decide) (by decide) (by decide) degreeP43 ?_
    degreeCheck43 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard43 rfl degreeCones43
    degreeTreeAll43 hr hn hh

end UniversalTensorSquare
end
end

end OAI
