import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover24
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions24

namespace OAI

/-! Degree Checks 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck24 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows24_0.length, ∀ c ∈ List.range degreeRows24_0.length,
      semanticResidualCheck 24 4 7 (d+1) (e+1) (a+1) (c+1) degreeRows24_0 degreeP24 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked24 (degreeCover24 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
