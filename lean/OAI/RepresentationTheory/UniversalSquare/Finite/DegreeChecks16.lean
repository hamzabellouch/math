import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover16
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions16

namespace OAI

/-! Degree Checks 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck16 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows16_0.length, ∀ c ∈ List.range degreeRows16_0.length,
      semanticResidualCheck 16 4 3 (d+1) (e+1) (a+1) (c+1) degreeRows16_0 degreeP16 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked16 (degreeCover16 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
