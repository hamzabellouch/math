import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks22
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof22

namespace OAI

/-! Numerical Degree 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos22 (μ : YoungDiagram) (hμ : μ.card = 22) :
    0 < kronecker (canonicalTableau (candidate 4 3 0) degreeCard22)
      (canonicalTableau (candidate 4 3 0) degreeCard22) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 6) (by decide) (by decide) rfl (by decide)
    degreeCard22 degreeRows22_0 (by decide) (by decide)
    degreePlan22_0 (by decide) (by decide) (by decide) (by decide) degreeP22 ?_
    degreeCheck22 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard22 rfl degreeCones22
    degreeTreeAll22 hr hn hh

end UniversalTensorSquare
end
end

end OAI
