import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover58
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions58

namespace OAI

/-! Degree Checks 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck58 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows58_0.length, ∀ c ∈ List.range degreeRows58_0.length,
      semanticResidualCheck 58 8 11 (d+1) (e+1) (a+1) (c+1) degreeRows58_0 degreeP58 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked58 (degreeCover58 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
