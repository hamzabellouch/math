import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree20_0 : RowTree := (.node [6,2,2,2,2,1,1,1,1,1,1] (.node [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [5,5,4,3,3] (.node [5,4,4,4,3] (.node [4,4,4,4,4] .empty .empty) .empty) (.node [5,5,4,4,2] .empty .empty)) (.node [6,2,2,1,1,1,1,1,1,1,1,1,1] (.node [6,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,2,2,2,1,1,1,1,1,1,1,1] .empty .empty))) (.node [6,3,1,1,1,1,1,1,1,1,1,1,1] (.node [6,2,2,2,2,2,2,1,1] (.node [6,2,2,2,2,2,1,1,1,1] .empty .empty) (.node [6,2,2,2,2,2,2,2] .empty .empty)) (.node [6,3,2,2,1,1,1,1,1,1,1] (.node [6,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,3,2,2,2,1,1,1,1,1] .empty .empty))))

def degreeTree20_1 : RowTree := (.node [6,3,3,3,2,2,1] (.node [6,3,3,2,2,2,1,1] (.node [6,3,3,2,1,1,1,1,1,1] (.node [6,3,3,1,1,1,1,1,1,1,1] (.node [6,3,2,2,2,2,2,1] .empty .empty) .empty) (.node [6,3,3,2,2,1,1,1,1] .empty .empty)) (.node [6,3,3,3,1,1,1,1,1] (.node [6,3,3,2,2,2,2] .empty .empty) (.node [6,3,3,3,2,1,1,1] .empty .empty))) (.node [6,4,2,1,1,1,1,1,1,1,1] (.node [6,3,3,3,3,2] (.node [6,3,3,3,3,1,1] .empty .empty) (.node [6,4,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [6,4,2,2,2,1,1,1,1] (.node [6,4,2,2,1,1,1,1,1,1] .empty .empty) (.node [6,4,2,2,2,2,1,1] .empty .empty))))

def degreeTree20_2 : RowTree := (.node [6,3,2,2,2,2,1,1,1] degreeTree20_0 degreeTree20_1)

def degreeTree20_3 : RowTree := (.node [6,4,4,1,1,1,1,1,1] (.node [6,4,3,3,1,1,1,1] (.node [6,4,3,2,2,1,1,1] (.node [6,4,3,2,1,1,1,1,1] (.node [6,4,3,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [6,4,3,2,2,2,1] .empty .empty)) (.node [6,4,3,3,2,2] (.node [6,4,3,3,2,1,1] .empty .empty) (.node [6,4,3,3,3,1] .empty .empty))) (.node [6,4,4,3,1,1,1] (.node [6,4,4,2,2,1,1] (.node [6,4,4,2,1,1,1,1] .empty .empty) (.node [6,4,4,2,2,2] .empty .empty)) (.node [6,4,4,4,1,1] (.node [6,4,4,3,2,1] .empty .empty) (.node [6,5,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree20_4 : RowTree := (.node [6,5,3,3,1,1,1] (.node [6,5,3,1,1,1,1,1,1] (.node [6,5,2,2,2,1,1,1] (.node [6,5,2,2,1,1,1,1,1] .empty .empty) (.node [6,5,2,2,2,2,1] .empty .empty)) (.node [6,5,3,2,2,1,1] (.node [6,5,3,2,1,1,1,1] .empty .empty) (.node [6,5,3,2,2,2] .empty .empty))) (.node [6,5,5,1,1,1,1] (.node [6,5,4,1,1,1,1,1] (.node [6,5,3,3,2,1] .empty .empty) (.node [6,5,4,2,1,1,1] .empty .empty)) (.node [6,6,2,1,1,1,1,1,1] (.node [6,6,1,1,1,1,1,1,1,1] .empty .empty) (.node [6,6,2,2,1,1,1,1] .empty .empty))))

def degreeTree20_5 : RowTree := (.node [6,5,2,1,1,1,1,1,1,1] degreeTree20_3 degreeTree20_4)

def degreeTree20_6 : RowTree := (.node [6,4,2,2,2,2,2] degreeTree20_2 degreeTree20_5)

def degreeTree20_7 : RowTree := (.node [7,2,2,2,2,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [6,6,3,2,1,1,1] (.node [6,6,3,1,1,1,1,1] (.node [6,6,2,2,2,2] .empty .empty) .empty) (.node [6,6,4,1,1,1,1] .empty .empty)) (.node [7,2,2,1,1,1,1,1,1,1,1,1] (.node [7,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,2,2,2,1,1,1,1,1,1,1] .empty .empty))) (.node [7,3,2,1,1,1,1,1,1,1,1] (.node [7,2,2,2,2,2,2,1] (.node [7,2,2,2,2,2,1,1,1] .empty .empty) (.node [7,3,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,3,2,2,2,1,1,1,1] (.node [7,3,2,2,1,1,1,1,1,1] .empty .empty) (.node [7,3,2,2,2,2,1,1] .empty .empty))))

def degreeTree20_8 : RowTree := (.node [7,4,2,1,1,1,1,1,1,1] (.node [7,3,3,2,2,2,1] (.node [7,3,3,2,1,1,1,1,1] (.node [7,3,3,1,1,1,1,1,1,1] .empty .empty) (.node [7,3,3,2,2,1,1,1] .empty .empty)) (.node [7,3,3,3,2,1,1] (.node [7,3,3,3,1,1,1,1] .empty .empty) (.node [7,4,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,4,3,1,1,1,1,1,1] (.node [7,4,2,2,2,1,1,1] (.node [7,4,2,2,1,1,1,1,1] .empty .empty) (.node [7,4,2,2,2,2,1] .empty .empty)) (.node [7,4,3,2,2,1,1] (.node [7,4,3,2,1,1,1,1] .empty .empty) (.node [7,4,3,3,1,1,1] .empty .empty))))

def degreeTree20_9 : RowTree := (.node [7,3,2,2,2,2,2] degreeTree20_7 degreeTree20_8)

def degreeTree20_10 : RowTree := (.node [8,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,5,3,1,1,1,1,1] (.node [7,5,2,2,1,1,1,1] (.node [7,5,2,1,1,1,1,1,1] (.node [7,5,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,5,2,2,2,1,1] .empty .empty)) (.node [7,6,2,1,1,1,1,1] (.node [7,6,1,1,1,1,1,1,1] .empty .empty) (.node [7,7,1,1,1,1,1,1] .empty .empty))) (.node [8,2,2,2,2,1,1,1,1] (.node [8,2,2,1,1,1,1,1,1,1,1] (.node [8,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,2,2,2,1,1,1,1,1,1] .empty .empty)) (.node [8,3,1,1,1,1,1,1,1,1,1] (.node [8,2,2,2,2,2,1,1] .empty .empty) (.node [8,3,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree20_11 : RowTree := (.node [9,1,1,1,1,1,1,1,1,1,1,1] (.node [8,4,1,1,1,1,1,1,1,1] (.node [8,3,3,1,1,1,1,1,1] (.node [8,3,2,2,2,1,1,1] .empty .empty) (.node [8,3,3,2,1,1,1,1] .empty .empty)) (.node [8,4,2,2,1,1,1,1] (.node [8,4,2,1,1,1,1,1,1] .empty .empty) (.node [8,5,1,1,1,1,1,1,1] .empty .empty))) (.node [9,3,1,1,1,1,1,1,1,1] (.node [9,2,2,1,1,1,1,1,1,1] (.node [9,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,2,2,2,1,1,1,1,1] .empty .empty)) (.node [10,1,1,1,1,1,1,1,1,1,1] (.node [9,3,2,1,1,1,1,1,1] .empty .empty) (.node [10,2,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree20_12 : RowTree := (.node [8,3,2,2,1,1,1,1,1] degreeTree20_10 degreeTree20_11)

def degreeTree20_13 : RowTree := (.node [7,4,4,1,1,1,1,1] degreeTree20_9 degreeTree20_12)

def degreeTree20_14 : RowTree := (.node [6,6,2,2,2,1,1] degreeTree20_6 degreeTree20_13)

def degreeTree20 : RowTree := degreeTree20_14

end UniversalTensorSquare
end
end

end OAI
