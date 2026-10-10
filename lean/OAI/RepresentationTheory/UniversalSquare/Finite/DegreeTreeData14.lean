import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree14_0 : RowTree := (.node [7,2,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1] .empty .empty) .empty)

def degreeTree14 : RowTree := degreeTree14_0

end UniversalTensorSquare
end
end

end OAI
