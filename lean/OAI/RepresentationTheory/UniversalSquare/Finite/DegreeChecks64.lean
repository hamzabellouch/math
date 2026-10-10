import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover64
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions64

namespace OAI

/-! Degree Checks 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck64 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows64_0.length, ∀ c ∈ List.range degreeRows64_0.length,
      semanticResidualCheck 64 8 14 (d+1) (e+1) (a+1) (c+1) degreeRows64_0 degreeP64 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked64 (degreeCover64 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
