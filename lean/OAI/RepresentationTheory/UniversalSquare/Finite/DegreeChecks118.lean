import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover118
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions118

namespace OAI

/-! Degree Checks 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck118 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows118_0.length, ∀ c ∈ List.range degreeRows118_0.length,
      semanticResidualCheck 118 12 20 (d+1) (e+1) (a+1) (c+1) degreeRows118_0 degreeP118 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked118 (degreeCover118 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
