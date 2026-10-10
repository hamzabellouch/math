import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeCover20
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegions20

namespace OAI

/-! Degree Checks 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck20 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows20_0.length, ∀ c ∈ List.range degreeRows20_0.length,
      semanticResidualCheck 20 4 5 (d+1) (e+1) (a+1) (c+1) degreeRows20_0 degreeP20 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked20 (degreeCover20 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
