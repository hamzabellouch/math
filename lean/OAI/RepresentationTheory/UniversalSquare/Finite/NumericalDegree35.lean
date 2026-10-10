import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks35
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof35

namespace OAI

/-! Numerical Degree 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos35 (μ : YoungDiagram) (hμ : μ.card = 35) :
    0 < kronecker (canonicalTableau (candidate 6 3 1) degreeCard35)
      (canonicalTableau (candidate 6 3 1) degreeCard35) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 7) (by decide) (by decide) rfl (by decide)
    degreeCard35 degreeRows35_0 (by decide) (by decide)
    degreePlan35_0 (by decide) (by decide) (by decide) (by decide) degreeP35 ?_
    degreeCheck35 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard35 rfl degreeCones35
    degreeTreeAll35 hr hn hh

end UniversalTensorSquare
end
end

end OAI
