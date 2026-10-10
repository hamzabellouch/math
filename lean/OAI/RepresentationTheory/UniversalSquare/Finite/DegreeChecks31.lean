import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover31
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions31

namespace OAI

/-! Degree Checks 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck31 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows31_0.length, ∀ c ∈ List.range degreeRows31_0.length,
      semanticResidualCheck 31 6 5 (d+1) (e+1) (a+1) (c+1) degreeRows31_0 degreeP31 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked31 (degreeCover31 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
