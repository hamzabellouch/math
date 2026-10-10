import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover41
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions41

namespace OAI

/-! Degree Checks 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck41 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows41_0.length, ∀ c ∈ List.range degreeRows41_0.length,
      semanticResidualCheck 41 6 10 (d+1) (e+1) (a+1) (c+1) degreeRows41_0 degreeP41 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked41 (degreeCover41 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
