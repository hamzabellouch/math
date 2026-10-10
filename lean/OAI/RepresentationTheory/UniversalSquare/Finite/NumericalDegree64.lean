import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeChecks64
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeProof64

namespace OAI

/-! Numerical Degree 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos64 (μ : YoungDiagram) (hμ : μ.card = 64) :
    0 < kronecker (canonicalTableau (candidate 8 7 0) degreeCard64)
      (canonicalTableau (candidate 8 7 0) degreeCard64) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 14) (by decide) (by decide) rfl (by decide)
    degreeCard64 degreeRows64_0 (by decide) (by decide)
    degreePlan64_0 (by decide) (by decide) (by decide) (by decide) degreeP64 ?_
    degreeCheck64 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard64 rfl degreeCones64
    degreeTreeAll64 hr hn hh

end UniversalTensorSquare
end
end

end OAI
