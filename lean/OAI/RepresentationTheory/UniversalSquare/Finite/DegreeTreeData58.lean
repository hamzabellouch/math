import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree58_0 : RowTree := (.node [10,9,9,9,9,4,2,1,1,1,1,1,1] (.node [10,9,9,9,9,2,2,2,2,2,1,1] (.node [10,9,9,9,8,7,1,1,1,1,1,1] (.node [9,9,9,9,9,7,1,1,1,1,1,1] (.node [9,9,9,9,8,8,1,1,1,1,1,1] .empty .empty) (.node [10,9,9,8,8,8,1,1,1,1,1,1] .empty .empty)) (.node [10,9,9,9,9,2,2,2,2,1,1,1,1] (.node [10,9,9,9,9,2,2,2,1,1,1,1,1,1] .empty .empty) .empty)) (.node [10,9,9,9,9,3,3,1,1,1,1,1,1] (.node [10,9,9,9,9,3,2,2,1,1,1,1,1] (.node [10,9,9,9,9,3,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,9,9,9,9,3,2,2,2,1,1,1] .empty .empty)) (.node [10,9,9,9,9,4,1,1,1,1,1,1,1,1] (.node [10,9,9,9,9,3,3,2,1,1,1,1] .empty .empty) .empty))) (.node [11,9,9,8,8,7,1,1,1,1,1,1] (.node [10,9,9,9,9,5,2,1,1,1,1,1] (.node [10,9,9,9,9,4,3,1,1,1,1,1] (.node [10,9,9,9,9,4,2,2,1,1,1,1] .empty .empty) (.node [10,9,9,9,9,5,1,1,1,1,1,1,1] .empty .empty)) (.node [11,9,8,8,8,8,1,1,1,1,1,1] (.node [10,9,9,9,9,6,1,1,1,1,1,1] .empty .empty) .empty)) (.node [11,9,9,9,8,2,2,2,2,2,1,1] (.node [11,9,9,9,8,2,2,2,1,1,1,1,1,1] (.node [11,9,9,9,7,7,1,1,1,1,1,1] .empty .empty) (.node [11,9,9,9,8,2,2,2,2,1,1,1,1] .empty .empty)) (.node [11,9,9,9,8,3,2,2,1,1,1,1,1] (.node [11,9,9,9,8,3,2,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree58_1 : RowTree := (.node [11,9,9,9,9,3,2,1,1,1,1,1,1] (.node [11,9,9,9,8,5,1,1,1,1,1,1,1] (.node [11,9,9,9,8,4,2,1,1,1,1,1,1] (.node [11,9,9,9,8,3,3,2,1,1,1,1] (.node [11,9,9,9,8,3,3,1,1,1,1,1,1] .empty .empty) (.node [11,9,9,9,8,4,1,1,1,1,1,1,1,1] .empty .empty)) (.node [11,9,9,9,8,4,3,1,1,1,1,1] (.node [11,9,9,9,8,4,2,2,1,1,1,1] .empty .empty) .empty)) (.node [11,9,9,9,9,2,2,2,1,1,1,1,1] (.node [11,9,9,9,8,6,1,1,1,1,1,1] (.node [11,9,9,9,8,5,2,1,1,1,1,1] .empty .empty) (.node [11,9,9,9,9,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [11,9,9,9,9,3,1,1,1,1,1,1,1,1] (.node [11,9,9,9,9,2,2,2,2,1,1,1] .empty .empty) .empty))) (.node [13,8,7,7,7,7,2,1,1,1,1,1,1,1] (.node [11,9,9,9,9,4,2,1,1,1,1,1] (.node [11,9,9,9,9,3,3,1,1,1,1,1] (.node [11,9,9,9,9,3,2,2,1,1,1,1] .empty .empty) (.node [11,9,9,9,9,4,1,1,1,1,1,1,1] .empty .empty)) (.node [12,9,7,7,7,7,2,1,1,1,1,1,1,1] (.node [11,9,9,9,9,5,1,1,1,1,1,1] .empty .empty) .empty)) (.node [14,7,7,6,6,6,5,1,1,1,1,1,1,1] (.node [13,9,7,7,7,7,1,1,1,1,1,1,1,1] (.node [13,9,7,7,7,6,2,1,1,1,1,1,1,1] .empty .empty) (.node [14,7,6,6,6,6,6,1,1,1,1,1,1,1] .empty .empty)) (.node [14,7,7,7,6,6,4,1,1,1,1,1,1,1] (.node [14,7,7,7,6,5,5,1,1,1,1,1,1,1] .empty .empty) .empty))))

def degreeTree58_2 : RowTree := (.node [11,9,9,9,8,3,2,2,2,1,1,1] degreeTree58_0 degreeTree58_1)

def degreeTree58 : RowTree := degreeTree58_2

end UniversalTensorSquare
end
end

end OAI
