import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover14
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions14

namespace OAI

/-! Degree Checks 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck14 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows14_0.length, ∀ c ∈ List.range degreeRows14_0.length,
      semanticResidualCheck 14 4 2 (d+1) (e+1) (a+1) (c+1) degreeRows14_0 degreeP14 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked14 (degreeCover14 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
