import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover26
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions26

namespace OAI

/-! Degree Checks 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck26 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      semanticResidualCheck 26 4 8 (d+1) (e+1) (a+1) (c+1) degreeRows26_0 degreeP26 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked26 (degreeCover26 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
