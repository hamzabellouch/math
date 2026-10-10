import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover62
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions62

namespace OAI

/-! Degree Checks 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck62 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      semanticResidualCheck 62 8 13 (d+1) (e+1) (a+1) (c+1) degreeRows62_0 degreeP62 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked62 (degreeCover62 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
