import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover39
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions39

namespace OAI

/-! Degree Checks 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck39 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows39_0.length, ∀ c ∈ List.range degreeRows39_0.length,
      semanticResidualCheck 39 6 9 (d+1) (e+1) (a+1) (c+1) degreeRows39_0 degreeP39 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked39 (degreeCover39 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
