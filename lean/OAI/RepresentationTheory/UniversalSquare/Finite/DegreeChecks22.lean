import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover22
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions22

namespace OAI

/-! Degree Checks 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck22 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows22_0.length, ∀ c ∈ List.range degreeRows22_0.length,
      semanticResidualCheck 22 4 6 (d+1) (e+1) (a+1) (c+1) degreeRows22_0 degreeP22 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked22 (degreeCover22 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
