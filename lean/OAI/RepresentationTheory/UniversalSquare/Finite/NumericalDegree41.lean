import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks41
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof41

namespace OAI

/-! Numerical Degree 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos41 (μ : YoungDiagram) (hμ : μ.card = 41) :
    0 < kronecker (canonicalTableau (candidate 6 5 0) degreeCard41)
      (canonicalTableau (candidate 6 5 0) degreeCard41) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 10) (by decide) (by decide) rfl (by decide)
    degreeCard41 degreeRows41_0 (by decide) (by decide)
    degreePlan41_0 (by decide) (by decide) (by decide) (by decide) degreeP41 ?_
    degreeCheck41 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard41 rfl degreeCones41
    degreeTreeAll41 hr hn hh

end UniversalTensorSquare
end
end

end OAI
