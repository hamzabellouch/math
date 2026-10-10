import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks39
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof39

namespace OAI

/-! Numerical Degree 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos39 (μ : YoungDiagram) (hμ : μ.card = 39) :
    0 < kronecker (canonicalTableau (candidate 6 4 1) degreeCard39)
      (canonicalTableau (candidate 6 4 1) degreeCard39) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 9) (by decide) (by decide) rfl (by decide)
    degreeCard39 degreeRows39_0 (by decide) (by decide)
    degreePlan39_0 (by decide) (by decide) (by decide) (by decide) degreeP39 ?_
    degreeCheck39 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard39 rfl degreeCones39
    degreeTreeAll39 hr hn hh

end UniversalTensorSquare
end
end

end OAI
