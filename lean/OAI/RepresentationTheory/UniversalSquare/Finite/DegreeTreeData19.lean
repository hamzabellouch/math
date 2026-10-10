import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree19_0 : RowTree := (.node [8,3,2,2,1,1,1,1] (.node [8,2,2,2,2,1,1,1] .empty .empty) (.node [8,3,3,1,1,1,1,1] .empty .empty))

def degreeTree19 : RowTree := degreeTree19_0

end UniversalTensorSquare
end
end

end OAI
