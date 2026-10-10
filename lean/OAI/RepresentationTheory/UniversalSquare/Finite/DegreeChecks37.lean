import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover37
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions37

namespace OAI

/-! Degree Checks 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck37 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows37_0.length, ∀ c ∈ List.range degreeRows37_0.length,
      semanticResidualCheck 37 6 8 (d+1) (e+1) (a+1) (c+1) degreeRows37_0 degreeP37 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked37 (degreeCover37 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
