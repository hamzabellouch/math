import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 118. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree118_0 : RowTree := (.node [11,11,11,11,11,11,11,11,11,10,9] (.node [11,11,11,11,11,11,11,11,10,10,10] .empty .empty) .empty)

def degreeTree118 : RowTree := degreeTree118_0

end UniversalTensorSquare
end
end

end OAI
