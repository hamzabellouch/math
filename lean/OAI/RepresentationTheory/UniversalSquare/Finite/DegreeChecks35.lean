import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover35
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions35

namespace OAI

/-! Degree Checks 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck35 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows35_0.length, ∀ c ∈ List.range degreeRows35_0.length,
      semanticResidualCheck 35 6 7 (d+1) (e+1) (a+1) (c+1) degreeRows35_0 degreeP35 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked35 (degreeCover35 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
