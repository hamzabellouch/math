import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree22_0 : RowTree := (.node [7,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,2,2,2,1,1,1,1,1,1,1] (.node [7,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,2,2,2,2,2,2,1,1,1] (.node [7,2,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [7,2,2,2,2,2,2,2,1] .empty .empty))) (.node [7,3,2,2,2,2,2,1,1] (.node [7,3,2,2,2,1,1,1,1,1,1] (.node [7,3,2,2,1,1,1,1,1,1,1,1] (.node [7,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,3,2,2,2,2,1,1,1,1] .empty .empty)) (.node [7,3,3,1,1,1,1,1,1,1,1,1] (.node [7,3,2,2,2,2,2,2] .empty .empty) (.node [7,3,3,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_1 : RowTree := (.node [7,4,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,3,3,2,2,1,1] (.node [7,3,3,3,1,1,1,1,1,1] (.node [7,3,3,2,2,2,2,1] (.node [7,3,3,2,2,2,1,1,1] .empty .empty) .empty) (.node [7,3,3,3,2,1,1,1,1] .empty .empty)) (.node [7,3,3,3,3,1,1,1] (.node [7,3,3,3,2,2,2] .empty .empty) (.node [7,3,3,3,3,2,1] .empty .empty))) (.node [7,4,2,2,2,2,1,1,1] (.node [7,4,2,2,1,1,1,1,1,1,1] (.node [7,4,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,4,2,2,2,1,1,1,1,1] .empty .empty)) (.node [7,4,3,1,1,1,1,1,1,1,1] (.node [7,4,2,2,2,2,2,1] .empty .empty) (.node [7,4,3,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_2 : RowTree := (.node [7,3,3,2,2,1,1,1,1,1] degreeTree22_0 degreeTree22_1)

def degreeTree22_3 : RowTree := (.node [7,4,4,2,2,1,1,1] (.node [7,4,3,3,2,2,1] (.node [7,4,3,3,1,1,1,1,1] (.node [7,4,3,2,2,2,2] (.node [7,4,3,2,2,2,1,1] .empty .empty) .empty) (.node [7,4,3,3,2,1,1,1] .empty .empty)) (.node [7,4,4,1,1,1,1,1,1,1] (.node [7,4,3,3,3,1,1] .empty .empty) (.node [7,4,4,2,1,1,1,1,1] .empty .empty))) (.node [7,4,4,4,1,1,1] (.node [7,4,4,3,1,1,1,1] (.node [7,4,4,2,2,2,1] .empty .empty) (.node [7,4,4,3,2,1,1] .empty .empty)) (.node [7,5,2,1,1,1,1,1,1,1,1] (.node [7,5,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,5,2,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_4 : RowTree := (.node [7,5,4,1,1,1,1,1,1] (.node [7,5,3,2,2,1,1,1] (.node [7,5,3,1,1,1,1,1,1,1] (.node [7,5,2,2,2,2,2] (.node [7,5,2,2,2,2,1,1] .empty .empty) .empty) (.node [7,5,3,2,1,1,1,1,1] .empty .empty)) (.node [7,5,3,3,1,1,1,1] (.node [7,5,3,2,2,2,1] .empty .empty) (.node [7,5,3,3,2,1,1] .empty .empty))) (.node [7,6,2,1,1,1,1,1,1,1] (.node [7,5,5,1,1,1,1,1] (.node [7,5,4,2,1,1,1,1] .empty .empty) (.node [7,6,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,6,2,2,2,1,1,1] (.node [7,6,2,2,1,1,1,1,1] .empty .empty) (.node [7,6,2,2,2,2,1] .empty .empty))))

def degreeTree22_5 : RowTree := (.node [7,5,2,2,2,1,1,1,1] degreeTree22_3 degreeTree22_4)

def degreeTree22_6 : RowTree := (.node [7,4,3,2,2,1,1,1,1] degreeTree22_2 degreeTree22_5)

def degreeTree22_7 : RowTree := (.node [8,2,2,1,1,1,1,1,1,1,1,1,1] (.node [7,7,2,2,1,1,1,1] (.node [7,7,1,1,1,1,1,1,1,1] (.node [7,6,4,1,1,1,1,1] (.node [7,6,3,2,1,1,1,1] .empty .empty) .empty) (.node [7,7,2,1,1,1,1,1,1] .empty .empty)) (.node [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,7,3,1,1,1,1,1] .empty .empty) (.node [8,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [8,2,2,2,2,2,2,2] (.node [8,2,2,2,2,2,1,1,1,1] (.node [8,2,2,2,2,1,1,1,1,1,1] (.node [8,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,2,2,2,2,2,2,1,1] .empty .empty)) (.node [8,3,2,1,1,1,1,1,1,1,1,1] (.node [8,3,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,3,2,2,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_8 : RowTree := (.node [8,4,1,1,1,1,1,1,1,1,1,1] (.node [8,3,3,2,2,1,1,1,1] (.node [8,3,3,1,1,1,1,1,1,1,1] (.node [8,3,2,2,2,2,2,1] (.node [8,3,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [8,3,3,2,1,1,1,1,1,1] .empty .empty)) (.node [8,3,3,3,1,1,1,1,1] (.node [8,3,3,2,2,2,1,1] .empty .empty) (.node [8,3,3,3,2,1,1,1] .empty .empty))) (.node [8,4,2,2,2,2,1,1] (.node [8,4,2,2,1,1,1,1,1,1] (.node [8,4,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,2,2,2,1,1,1,1] .empty .empty)) (.node [8,4,3,2,1,1,1,1,1] (.node [8,4,3,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,3,2,2,1,1,1] .empty .empty))))

def degreeTree22_9 : RowTree := (.node [8,3,2,2,2,1,1,1,1,1] degreeTree22_7 degreeTree22_8)

def degreeTree22_10 : RowTree := (.node [8,7,1,1,1,1,1,1,1] (.node [8,5,2,2,2,1,1,1] (.node [8,5,2,1,1,1,1,1,1,1] (.node [8,5,1,1,1,1,1,1,1,1,1] (.node [8,4,4,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,5,2,2,1,1,1,1,1] .empty .empty)) (.node [8,6,1,1,1,1,1,1,1,1] (.node [8,5,3,1,1,1,1,1,1] .empty .empty) (.node [8,6,2,1,1,1,1,1,1] .empty .empty))) (.node [9,2,2,2,1,1,1,1,1,1,1] (.node [9,2,1,1,1,1,1,1,1,1,1,1,1] (.node [9,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [9,2,2,2,2,2,1,1,1] (.node [9,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [9,3,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_11 : RowTree := (.node [10,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,4,1,1,1,1,1,1,1,1,1] (.node [9,3,3,1,1,1,1,1,1,1] (.node [9,3,2,2,2,1,1,1,1] (.node [9,3,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [9,3,3,2,1,1,1,1,1] .empty .empty)) (.node [9,4,2,2,1,1,1,1,1] (.node [9,4,2,1,1,1,1,1,1,1] .empty .empty) (.node [9,5,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,3,1,1,1,1,1,1,1,1,1] (.node [10,2,2,1,1,1,1,1,1,1,1] (.node [10,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,2,2,2,1,1,1,1,1,1] .empty .empty)) (.node [11,1,1,1,1,1,1,1,1,1,1,1] (.node [10,3,2,1,1,1,1,1,1,1] .empty .empty) (.node [11,2,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree22_12 : RowTree := (.node [9,3,2,1,1,1,1,1,1,1,1] degreeTree22_10 degreeTree22_11)

def degreeTree22_13 : RowTree := (.node [8,4,3,3,1,1,1,1] degreeTree22_9 degreeTree22_12)

def degreeTree22_14 : RowTree := (.node [7,6,3,1,1,1,1,1,1] degreeTree22_6 degreeTree22_13)

def degreeTree22 : RowTree := degreeTree22_14

end UniversalTensorSquare
end
end

end OAI
