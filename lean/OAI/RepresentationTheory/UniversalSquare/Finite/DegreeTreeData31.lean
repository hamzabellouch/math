import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree31_0 : RowTree := (.node [10,3,3,3,2,2,2,2,2,2] (.node [9,9,3,2,2,2,1,1,1,1] (.node [9,8,6,2,1,1,1,1,1,1] (.node [8,8,8,1,1,1,1,1,1,1] (.node [8,8,7,2,1,1,1,1,1,1] .empty .empty) (.node [9,7,7,2,1,1,1,1,1,1] .empty .empty)) (.node [9,9,2,2,2,2,2,1,1,1] (.node [9,8,7,1,1,1,1,1,1,1] .empty .empty) .empty)) (.node [9,9,4,3,1,1,1,1,1,1] (.node [9,9,4,2,2,1,1,1,1,1] (.node [9,9,3,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [9,9,6,1,1,1,1,1,1,1] (.node [9,9,5,2,1,1,1,1,1,1] .empty .empty) .empty))) (.node [10,4,3,3,3,2,2,2,1,1] (.node [10,3,3,3,3,3,3,1,1,1] (.node [10,3,3,3,3,3,2,2,1,1] (.node [10,3,3,3,3,2,2,2,2,1] .empty .empty) .empty) (.node [10,4,3,3,2,2,2,2,2,1] (.node [10,4,3,2,2,2,2,2,2,2] .empty .empty) .empty)) (.node [10,4,4,3,2,2,2,2,1,1] (.node [10,4,4,2,2,2,2,2,2,1] (.node [10,4,3,3,3,3,2,1,1,1] .empty .empty) .empty) (.node [10,4,4,3,3,3,1,1,1,1] (.node [10,4,4,3,3,2,2,1,1,1] .empty .empty) .empty))))

def degreeTree31_1 : RowTree := (.node [10,5,4,4,3,1,1,1,1,1] (.node [10,5,3,3,3,2,2,1,1,1] (.node [10,5,2,2,2,2,2,2,2,2] (.node [10,4,4,4,4,1,1,1,1,1] (.node [10,4,4,4,3,2,1,1,1,1] .empty .empty) .empty) (.node [10,5,3,3,2,2,2,2,1,1] (.node [10,5,3,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [10,5,4,3,2,2,2,1,1,1] (.node [10,5,4,2,2,2,2,2,1,1] (.node [10,5,3,3,3,3,1,1,1,1] .empty .empty) .empty) (.node [10,5,4,4,2,2,1,1,1,1] (.node [10,5,4,3,3,2,1,1,1,1] .empty .empty) .empty))) (.node [10,6,3,3,2,2,2,1,1,1] (.node [10,5,5,3,3,1,1,1,1,1] (.node [10,5,5,3,2,2,1,1,1,1] (.node [10,5,5,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [10,6,3,2,2,2,2,2,1,1] (.node [10,6,2,2,2,2,2,2,2,1] .empty .empty) .empty)) (.node [10,6,4,3,2,2,1,1,1,1] (.node [10,6,4,2,2,2,2,1,1,1] (.node [10,6,3,3,3,2,1,1,1,1] .empty .empty) .empty) (.node [10,7,3,2,2,2,2,1,1,1] (.node [10,7,2,2,2,2,2,2,1,1] .empty .empty) .empty))))

def degreeTree31_2 : RowTree := (.node [10,4,4,4,2,2,2,1,1,1] degreeTree31_0 degreeTree31_1)

def degreeTree31 : RowTree := degreeTree31_2

end UniversalTensorSquare
end
end

end OAI
