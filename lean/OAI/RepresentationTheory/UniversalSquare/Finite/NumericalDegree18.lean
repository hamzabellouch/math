import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks18
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof18

namespace OAI

/-! Numerical Degree 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos18 (μ : YoungDiagram) (hμ : μ.card = 18) :
    0 < kronecker (canonicalTableau (candidate 4 2 0) degreeCard18)
      (canonicalTableau (candidate 4 2 0) degreeCard18) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard18 degreeRows18_0 (by decide) (by decide)
    degreePlan18_0 (by decide) (by decide) (by decide) (by decide) degreeP18 ?_
    degreeCheck18 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard18 rfl degreeCones18
    degreeTreeAll18 hr hn hh

end UniversalTensorSquare
end
end

end OAI
