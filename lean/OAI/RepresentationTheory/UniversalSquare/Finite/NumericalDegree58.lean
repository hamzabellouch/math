import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks58
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof58

namespace OAI

/-! Numerical Degree 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos58 (μ : YoungDiagram) (hμ : μ.card = 58) :
    0 < kronecker (canonicalTableau (candidate 8 5 1) degreeCard58)
      (canonicalTableau (candidate 8 5 1) degreeCard58) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 11) (by decide) (by decide) rfl (by decide)
    degreeCard58 degreeRows58_0 (by decide) (by decide)
    degreePlan58_0 (by decide) (by decide) (by decide) (by decide) degreeP58 ?_
    degreeCheck58 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard58 rfl degreeCones58
    degreeTreeAll58 hr hn hh

end UniversalTensorSquare
end
end

end OAI
