import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree16_0 : RowTree := (.node [6,4,1,1,1,1,1,1] (.node [6,3,1,1,1,1,1,1,1] (.node [6,2,2,2,1,1,1,1] (.node [6,2,1,1,1,1,1,1,1,1] (.node [6,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,2,2,1,1,1,1,1,1] .empty .empty)) (.node [6,2,2,2,2,2] (.node [6,2,2,2,2,1,1] .empty .empty) .empty)) (.node [6,3,2,2,2,1] (.node [6,3,2,2,1,1,1] (.node [6,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [6,3,3,2,1,1] (.node [6,3,3,1,1,1,1] .empty .empty) .empty))) (.node [7,2,2,1,1,1,1,1] (.node [6,5,1,1,1,1,1] (.node [6,4,2,2,1,1] (.node [6,4,2,1,1,1,1] .empty .empty) .empty) (.node [7,2,1,1,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [7,3,2,1,1,1,1] (.node [7,3,1,1,1,1,1,1] (.node [7,2,2,2,1,1,1] .empty .empty) .empty) (.node [8,2,1,1,1,1,1,1] (.node [8,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree16 : RowTree := degreeTree16_0

end UniversalTensorSquare
end
end

end OAI
