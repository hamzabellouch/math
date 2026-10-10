import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks20
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof20

namespace OAI

/-! Numerical Degree 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos20 (μ : YoungDiagram) (hμ : μ.card = 20) :
    0 < kronecker (canonicalTableau (candidate 4 2 1) degreeCard20)
      (canonicalTableau (candidate 4 2 1) degreeCard20) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 5) (by decide) (by decide) rfl (by decide)
    degreeCard20 degreeRows20_0 (by decide) (by decide)
    degreePlan20_0 (by decide) (by decide) (by decide) (by decide) degreeP20 ?_
    degreeCheck20 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard20 rfl degreeCones20
    degreeTreeAll20 hr hn hh

end UniversalTensorSquare
end
end

end OAI
