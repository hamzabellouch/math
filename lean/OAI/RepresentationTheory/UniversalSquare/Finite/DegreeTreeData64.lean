import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree64_0 : RowTree := (.node [13,11,10,9,3,2,2,2,2,2,2,2,2,2] (.node [12,11,10,10,3,2,2,2,2,2,2,2,2,2] (.node [11,11,11,10,3,2,2,2,2,2,2,2,2,2] (.node [8,8,8,8,8,8,8,8] .empty .empty) (.node [11,11,11,11,2,2,2,2,2,2,2,2,2,2] .empty .empty)) (.node [12,11,11,10,2,2,2,2,2,2,2,2,2,2] (.node [12,11,11,9,3,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [13,10,10,10,3,2,2,2,2,2,2,2,2,2] .empty .empty))) (.node [13,12,9,9,3,2,2,2,2,2,2,2,2,2] (.node [13,11,11,8,3,2,2,2,2,2,2,2,2,2] (.node [13,11,10,10,2,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [13,11,11,9,2,2,2,2,2,2,2,2,2,2] .empty .empty)) (.node [13,13,9,9,2,2,2,2,2,2,2,2,2,2] (.node [13,13,9,8,3,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [14,11,9,9,3,2,2,2,2,2,2,2,2,2] .empty .empty))))

def degreeTree64 : RowTree := degreeTree64_0

end UniversalTensorSquare
end
end

end OAI
