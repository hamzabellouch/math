import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover116
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions116

namespace OAI

/-! Degree Checks 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck116 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows116_0.length, ∀ c ∈ List.range degreeRows116_0.length,
      semanticResidualCheck 116 12 19 (d+1) (e+1) (a+1) (c+1) degreeRows116_0 degreeP116 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked116 (degreeCover116 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
