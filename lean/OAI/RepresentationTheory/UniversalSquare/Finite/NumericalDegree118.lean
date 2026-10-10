import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks118
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof118

namespace OAI

/-! Numerical Degree 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos118 (μ : YoungDiagram) (hμ : μ.card = 118) :
    0 < kronecker (canonicalTableau (candidate 12 10 0) degreeCard118)
      (canonicalTableau (candidate 12 10 0) degreeCard118) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 20) (by decide) (by decide) rfl (by decide)
    degreeCard118 degreeRows118_0 (by decide) (by decide)
    degreePlan118_0 (by decide) (by decide) (by decide) (by decide) degreeP118 ?_
    degreeCheck118 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard118 rfl degreeCones118
    degreeTreeAll118 hr hn hh

end UniversalTensorSquare
end
end

end OAI
