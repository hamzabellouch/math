import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover19
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions19

namespace OAI

/-! Degree Checks 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck19 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows19_0.length, ∀ c ∈ List.range degreeRows19_0.length,
      semanticResidualCheck 19 5 2 (d+1) (e+1) (a+1) (c+1) degreeRows19_0 degreeP19 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked19 (degreeCover19 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
