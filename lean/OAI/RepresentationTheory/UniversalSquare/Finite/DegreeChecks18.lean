import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover18
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions18

namespace OAI

/-! Degree Checks 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck18 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      semanticResidualCheck 18 4 4 (d+1) (e+1) (a+1) (c+1) degreeRows18_0 degreeP18 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked18 (degreeCover18 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
