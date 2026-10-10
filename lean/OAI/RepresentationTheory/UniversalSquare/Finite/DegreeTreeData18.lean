import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree18_0 : RowTree := (.node [7,4,1,1,1,1,1,1,1] (.node [7,3,1,1,1,1,1,1,1,1] (.node [7,2,2,2,1,1,1,1,1] (.node [7,2,1,1,1,1,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [7,2,2,2,2,2,1] (.node [7,2,2,2,2,1,1,1] .empty .empty) .empty)) (.node [7,3,2,2,2,1,1] (.node [7,3,2,2,1,1,1,1] (.node [7,3,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,3,3,2,1,1,1] (.node [7,3,3,1,1,1,1,1] .empty .empty) .empty))) (.node [8,2,2,1,1,1,1,1,1] (.node [7,5,1,1,1,1,1,1] (.node [7,4,2,2,1,1,1] (.node [7,4,2,1,1,1,1,1] .empty .empty) .empty) (.node [8,2,1,1,1,1,1,1,1,1] (.node [8,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [8,3,2,1,1,1,1,1] (.node [8,3,1,1,1,1,1,1,1] (.node [8,2,2,2,1,1,1,1] .empty .empty) .empty) (.node [9,2,1,1,1,1,1,1,1] (.node [9,1,1,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree18 : RowTree := degreeTree18_0

end UniversalTensorSquare
end
end

end OAI
