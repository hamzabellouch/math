import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks14
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof14

namespace OAI

/-! Numerical Degree 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos14 (μ : YoungDiagram) (hμ : μ.card = 14) :
    0 < kronecker (canonicalTableau (candidate 4 1 0) degreeCard14)
      (canonicalTableau (candidate 4 1 0) degreeCard14) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 2) (by decide) (by decide) rfl (by decide)
    degreeCard14 degreeRows14_0 (by decide) (by decide)
    degreePlan14_0 (by decide) (by decide) (by decide) (by decide) degreeP14 ?_
    degreeCheck14 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard14 rfl degreeCones14
    degreeTreeAll14 hr hn hh

end UniversalTensorSquare
end
end

end OAI
