import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover43
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions43

namespace OAI

/-! Degree Checks 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck43 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows43_0.length, ∀ c ∈ List.range degreeRows43_0.length,
      semanticResidualCheck 43 6 11 (d+1) (e+1) (a+1) (c+1) degreeRows43_0 degreeP43 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked43 (degreeCover43 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
