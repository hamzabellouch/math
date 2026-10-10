import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks16
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof16

namespace OAI

/-! Numerical Degree 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos16 (μ : YoungDiagram) (hμ : μ.card = 16) :
    0 < kronecker (canonicalTableau (candidate 4 1 1) degreeCard16)
      (canonicalTableau (candidate 4 1 1) degreeCard16) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 3) (by decide) (by decide) rfl (by decide)
    degreeCard16 degreeRows16_0 (by decide) (by decide)
    degreePlan16_0 (by decide) (by decide) (by decide) (by decide) degreeP16 ?_
    degreeCheck16 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard16 rfl degreeCones16
    degreeTreeAll16 hr hn hh

end UniversalTensorSquare
end
end

end OAI
