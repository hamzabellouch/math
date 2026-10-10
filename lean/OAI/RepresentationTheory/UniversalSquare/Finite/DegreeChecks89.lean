import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover89
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions89

namespace OAI

/-! Degree Checks 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck89 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows89_0.length, ∀ c ∈ List.range degreeRows89_0.length,
      semanticResidualCheck 89 10 17 (d+1) (e+1) (a+1) (c+1) degreeRows89_0 degreeP89 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked89 (degreeCover89 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
