import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 116. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree116_0 : RowTree := (.node [11,11,11,11,11,11,11,11,10,9,9] (.node [11,11,11,11,11,11,11,10,10,10,9] (.node [11,11,11,11,11,11,10,10,10,10,10] .empty .empty) .empty) (.node [11,11,11,11,11,11,11,11,10,10,8] .empty .empty))

def degreeTree116 : RowTree := degreeTree116_0

end UniversalTensorSquare
end
end

end OAI
