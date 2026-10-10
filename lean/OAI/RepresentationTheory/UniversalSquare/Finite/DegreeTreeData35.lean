import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree35_0 : RowTree := (.node [8,8,7,4,3,1,1,1,1,1] (.node [8,8,7,2,2,2,2,2,2] (.node [8,8,6,6,2,1,1,1,1,1] (.node [8,7,7,7,1,1,1,1,1,1] (.node [8,7,7,6,2,1,1,1,1,1] .empty .empty) .empty) (.node [8,8,7,2,2,2,2,2,1,1] .empty .empty)) (.node [8,8,7,3,3,2,1,1,1,1] (.node [8,8,7,3,2,2,2,1,1,1] .empty .empty) (.node [8,8,7,4,2,2,1,1,1,1] .empty .empty))) (.node [8,8,8,3,2,2,1,1,1,1] (.node [8,8,7,6,1,1,1,1,1,1] (.node [8,8,7,5,2,1,1,1,1,1] .empty .empty) (.node [8,8,8,2,2,2,2,1,1,1] .empty .empty)) (.node [8,8,8,4,2,1,1,1,1,1] (.node [8,8,8,3,3,1,1,1,1,1] .empty .empty) (.node [8,8,8,5,1,1,1,1,1,1] .empty .empty))))

def degreeTree35_1 : RowTree := (.node [9,7,7,6,1,1,1,1,1,1] (.node [9,7,7,3,3,2,1,1,1,1] (.node [9,7,7,2,2,2,2,2,2] (.node [9,7,7,2,2,2,2,2,1,1] .empty .empty) (.node [9,7,7,3,2,2,2,1,1,1] .empty .empty)) (.node [9,7,7,4,3,1,1,1,1,1] (.node [9,7,7,4,2,2,1,1,1,1] .empty .empty) (.node [9,7,7,5,2,1,1,1,1,1] .empty .empty))) (.node [9,8,6,3,3,2,1,1,1,1] (.node [9,8,6,2,2,2,2,2,2] (.node [9,8,6,2,2,2,2,2,1,1] .empty .empty) (.node [9,8,6,3,2,2,2,1,1,1] .empty .empty)) (.node [9,8,6,4,3,1,1,1,1,1] (.node [9,8,6,4,2,2,1,1,1,1] .empty .empty) (.node [9,8,6,5,2,1,1,1,1,1] .empty .empty))))

def degreeTree35_2 : RowTree := (.node [9,7,6,6,2,1,1,1,1,1] degreeTree35_0 degreeTree35_1)

def degreeTree35_3 : RowTree := (.node [9,9,3,2,2,2,2,2,2,2] (.node [9,8,7,5,1,1,1,1,1,1] (.node [9,8,7,3,3,1,1,1,1,1] (.node [9,8,7,3,2,2,1,1,1,1] (.node [9,8,7,2,2,2,2,1,1,1] .empty .empty) .empty) (.node [9,8,7,4,2,1,1,1,1,1] .empty .empty)) (.node [9,8,8,3,2,1,1,1,1,1] (.node [9,8,8,2,2,2,1,1,1,1] .empty .empty) (.node [9,8,8,4,1,1,1,1,1,1] .empty .empty))) (.node [9,9,3,3,3,3,2,1,1,1] (.node [9,9,3,3,3,2,2,2,1,1] (.node [9,9,3,3,2,2,2,2,2,1] .empty .empty) (.node [9,9,3,3,3,2,2,2,2] .empty .empty)) (.node [9,9,4,3,2,2,2,2,1,1] (.node [9,9,4,2,2,2,2,2,2,1] .empty .empty) (.node [9,9,4,3,2,2,2,2,2] .empty .empty))))

def degreeTree35_4 : RowTree := (.node [9,9,5,4,2,2,1,1,1,1] (.node [9,9,4,4,4,1,1,1,1,1] (.node [9,9,4,4,2,2,2,1,1,1] (.node [9,9,4,3,3,3,1,1,1,1] .empty .empty) (.node [9,9,4,4,3,2,1,1,1,1] .empty .empty)) (.node [9,9,5,3,2,2,2,1,1,1] (.node [9,9,5,2,2,2,2,2,1,1] .empty .empty) (.node [9,9,5,3,3,2,1,1,1,1] .empty .empty))) (.node [9,9,6,3,2,2,1,1,1,1] (.node [9,9,5,5,2,1,1,1,1,1] (.node [9,9,5,4,3,1,1,1,1,1] .empty .empty) (.node [9,9,6,2,2,2,2,1,1,1] .empty .empty)) (.node [9,9,6,4,2,1,1,1,1,1] (.node [9,9,6,3,3,1,1,1,1,1] .empty .empty) (.node [9,9,6,5,1,1,1,1,1,1] .empty .empty))))

def degreeTree35_5 : RowTree := (.node [9,9,4,3,3,2,2,1,1,1] degreeTree35_3 degreeTree35_4)

def degreeTree35_6 : RowTree := (.node [9,8,6,6,1,1,1,1,1,1] degreeTree35_2 degreeTree35_5)

def degreeTree35_7 : RowTree := (.node [10,3,2,2,2,2,2,2,2,2,2,2,1,1] (.node [9,9,9,2,1,1,1,1,1,1] (.node [9,9,8,2,2,1,1,1,1,1] (.node [9,9,7,4,1,1,1,1,1,1] (.node [9,9,7,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [9,9,8,3,1,1,1,1,1,1] .empty .empty)) (.node [10,2,2,2,2,2,2,2,2,2,2,2,2,1] (.node [10,2,2,2,2,2,2,2,2,2,2,2,1,1,1] .empty .empty) (.node [10,3,2,2,2,2,2,2,2,2,2,1,1,1,1] .empty .empty))) (.node [10,3,3,2,2,2,2,2,2,2,2,2,1] (.node [10,3,3,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,3,2,2,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [10,3,3,2,2,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,3,3,3,2,2,2,2,2,2,1,1,1,1] (.node [10,3,3,3,2,2,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,3,3,3,2,2,2,2,2,2,2,1,1] .empty .empty))))

def degreeTree35_8 : RowTree := (.node [10,3,3,3,3,3,2,2,2,2,1,1] (.node [10,3,3,3,3,2,2,2,2,2,2,1] (.node [10,3,3,3,3,2,2,2,2,1,1,1,1,1] (.node [10,3,3,3,3,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,3,3,3,3,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,3,3,3,3,3,2,2,1,1,1,1,1,1] (.node [10,3,3,3,3,3,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,3,3,3,3,3,2,2,2,1,1,1,1] .empty .empty))) (.node [10,3,3,3,3,3,3,2,2,1,1,1] (.node [10,3,3,3,3,3,3,1,1,1,1,1,1,1] (.node [10,3,3,3,3,3,2,2,2,2,2] .empty .empty) (.node [10,3,3,3,3,3,3,2,1,1,1,1,1] .empty .empty)) (.node [10,3,3,3,3,3,3,3,1,1,1,1] (.node [10,3,3,3,3,3,3,2,2,2,1] .empty .empty) (.node [10,3,3,3,3,3,3,3,2,1,1] .empty .empty))))

def degreeTree35_9 : RowTree := (.node [10,3,3,3,2,2,2,2,2,2,2,2] degreeTree35_7 degreeTree35_8)

def degreeTree35_10 : RowTree := (.node [10,4,3,3,3,2,2,2,2,2,1,1] (.node [10,4,3,2,2,2,2,2,2,2,2,2] (.node [10,4,2,2,2,2,2,2,2,2,2,2,1] (.node [10,4,2,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,3,3,3,3,3,3,3,3,1] .empty .empty) (.node [10,4,2,2,2,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,4,3,2,2,2,2,2,2,2,1,1,1,1] (.node [10,4,3,2,2,2,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [10,4,3,2,2,2,2,2,2,2,2,1,1] .empty .empty))) (.node [10,4,3,3,2,2,2,2,2,2,2,1] (.node [10,4,3,3,2,2,2,2,2,1,1,1,1,1] (.node [10,4,3,3,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,3,3,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [10,4,3,3,3,2,2,2,1,1,1,1,1,1] (.node [10,4,3,3,3,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,3,3,3,2,2,2,2,1,1,1,1] .empty .empty)))) (.node [10,4,3,3,3,3,3,2,1,1,1,1] (.node [10,4,3,3,3,3,2,2,1,1,1,1,1] (.node [10,4,3,3,3,3,1,1,1,1,1,1,1,1,1] (.node [10,4,3,3,3,2,2,2,2,2,2] .empty .empty) (.node [10,4,3,3,3,3,2,1,1,1,1,1,1,1] .empty .empty)) (.node [10,4,3,3,3,3,2,2,2,2,1] (.node [10,4,3,3,3,3,2,2,2,1,1,1] .empty .empty) (.node [10,4,3,3,3,3,3,1,1,1,1,1,1] .empty .empty))) (.node [10,4,3,3,3,3,3,3,2,1] (.node [10,4,3,3,3,3,3,2,2,2] (.node [10,4,3,3,3,3,3,2,2,1,1] .empty .empty) (.node [10,4,3,3,3,3,3,3,1,1,1] .empty .empty)) (.node [10,4,4,2,2,2,2,2,2,1,1,1,1,1] (.node [10,4,4,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,2,2,2,2,2,2,2,1,1,1] .empty .empty)))))

def degreeTree35_11 : RowTree := (.node [10,3,3,3,3,3,3,3,2,2] degreeTree35_9 degreeTree35_10)

def degreeTree35_12 : RowTree := (.node [9,9,7,2,2,2,1,1,1,1] degreeTree35_6 degreeTree35_11)

def degreeTree35_13 : RowTree := (.node [10,4,4,3,3,2,2,2,2,1,1,1] (.node [10,4,4,3,2,2,2,2,2,2,2] (.node [10,4,4,3,2,2,2,2,2,1,1,1,1] (.node [10,4,4,3,2,2,2,2,1,1,1,1,1,1] (.node [10,4,4,3,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [10,4,4,3,2,2,2,2,2,2,1,1] .empty .empty)) (.node [10,4,4,3,3,2,2,1,1,1,1,1,1,1] (.node [10,4,4,3,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,3,3,2,2,2,1,1,1,1,1] .empty .empty))) (.node [10,4,4,3,3,3,2,2,1,1,1,1] (.node [10,4,4,3,3,3,1,1,1,1,1,1,1,1] (.node [10,4,4,3,3,2,2,2,2,2,1] .empty .empty) (.node [10,4,4,3,3,3,2,1,1,1,1,1,1] .empty .empty)) (.node [10,4,4,3,3,3,2,2,2,2] (.node [10,4,4,3,3,3,2,2,2,1,1] .empty .empty) (.node [10,4,4,3,3,3,3,1,1,1,1,1] .empty .empty))))

def degreeTree35_14 : RowTree := (.node [10,4,4,4,3,1,1,1,1,1,1,1,1,1,1] (.node [10,4,4,4,2,2,2,1,1,1,1,1,1,1] (.node [10,4,4,3,3,3,3,3,1,1] (.node [10,4,4,3,3,3,3,2,2,1] .empty .empty) (.node [10,4,4,4,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,4,4,4,2,2,2,2,2,1,1,1] (.node [10,4,4,4,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [10,4,4,4,2,2,2,2,2,2,1] .empty .empty))) (.node [10,4,4,4,3,2,2,2,2,1,1] (.node [10,4,4,4,3,2,2,1,1,1,1,1,1] (.node [10,4,4,4,3,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,4,3,2,2,2,1,1,1,1] .empty .empty)) (.node [10,4,4,4,3,3,1,1,1,1,1,1,1] (.node [10,4,4,4,3,2,2,2,2,2] .empty .empty) (.node [10,4,4,4,3,3,2,1,1,1,1,1] .empty .empty))))

def degreeTree35_15 : RowTree := (.node [10,4,4,3,3,3,3,2,1,1,1] degreeTree35_13 degreeTree35_14)

def degreeTree35_16 : RowTree := (.node [10,5,2,2,2,2,2,2,2,2,1,1,1,1] (.node [10,4,4,4,4,2,2,2,2,1] (.node [10,4,4,4,4,1,1,1,1,1,1,1,1,1] (.node [10,4,4,4,3,3,3,1,1,1,1] (.node [10,4,4,4,3,3,2,2,2,1] .empty .empty) (.node [10,4,4,4,3,3,3,2,1,1] .empty .empty)) (.node [10,4,4,4,4,2,2,1,1,1,1,1] (.node [10,4,4,4,4,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,4,4,2,2,2,1,1,1] .empty .empty))) (.node [10,4,4,4,4,3,3,1,1,1] (.node [10,4,4,4,4,3,2,1,1,1,1] (.node [10,4,4,4,4,3,1,1,1,1,1,1] .empty .empty) (.node [10,4,4,4,4,3,2,2,1,1] .empty .empty)) (.node [10,4,4,4,4,4,2,1,1,1] (.node [10,4,4,4,4,4,1,1,1,1,1] .empty .empty) (.node [10,5,2,2,2,2,2,2,2,1,1,1,1,1,1] .empty .empty)))) (.node [10,5,4,3,3,3,3,2,1,1] (.node [10,5,3,3,3,3,3,2,2,1] (.node [10,5,2,2,2,2,2,2,2,2,2,2] (.node [10,5,2,2,2,2,2,2,2,2,2,1,1] .empty .empty) (.node [10,5,3,3,3,3,2,2,2,2] .empty .empty)) (.node [10,5,4,3,3,2,2,2,2,2] (.node [10,5,3,3,3,3,3,3,1,1] .empty .empty) (.node [10,5,4,3,3,3,2,2,2,1] .empty .empty))) (.node [10,5,4,4,3,3,3,1,1,1] (.node [10,5,4,4,3,2,2,2,2,1] (.node [10,5,4,4,2,2,2,2,2,2] .empty .empty) (.node [10,5,4,4,3,3,2,2,1,1] .empty .empty)) (.node [10,5,4,4,4,3,2,1,1,1] (.node [10,5,4,4,4,2,2,2,1,1] .empty .empty) (.node [10,5,4,4,4,4,1,1,1,1] .empty .empty)))))

def degreeTree35_17 : RowTree := (.node [10,4,4,4,3,3,2,2,1,1,1] degreeTree35_15 degreeTree35_16)

def degreeTree35_18 : RowTree := (.node [10,5,5,5,2,2,2,2,1,1] (.node [10,5,5,4,3,2,2,2,1,1] (.node [10,5,5,3,3,3,3,1,1,1] (.node [10,5,5,3,3,3,2,2,1,1] (.node [10,5,5,3,3,2,2,2,2,1] .empty .empty) .empty) (.node [10,5,5,4,2,2,2,2,2,1] .empty .empty)) (.node [10,5,5,4,4,2,2,1,1,1] (.node [10,5,5,4,3,3,2,1,1,1] .empty .empty) (.node [10,5,5,4,4,3,1,1,1,1] .empty .empty))) (.node [10,5,5,5,5,1,1,1,1,1] (.node [10,5,5,5,3,3,1,1,1,1] (.node [10,5,5,5,3,2,2,1,1,1] .empty .empty) (.node [10,5,5,5,4,2,1,1,1,1] .empty .empty)) (.node [10,6,2,2,2,2,2,2,2,1,1,1,1,1] (.node [10,6,2,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,6,2,2,2,2,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree35_19 : RowTree := (.node [10,6,4,4,2,2,2,2,2,1] (.node [10,6,4,3,2,2,2,2,2,2] (.node [10,6,3,3,3,3,2,2,2,1] (.node [10,6,3,3,3,2,2,2,2,2] .empty .empty) (.node [10,6,3,3,3,3,3,2,1,1] .empty .empty)) (.node [10,6,4,3,3,3,2,2,1,1] (.node [10,6,4,3,3,2,2,2,2,1] .empty .empty) (.node [10,6,4,3,3,3,3,1,1,1] .empty .empty))) (.node [10,6,4,4,4,3,1,1,1,1] (.node [10,6,4,4,3,3,2,1,1,1] (.node [10,6,4,4,3,2,2,2,1,1] .empty .empty) (.node [10,6,4,4,4,2,2,1,1,1] .empty .empty)) (.node [10,6,5,3,2,2,2,2,2,1] (.node [10,6,5,2,2,2,2,2,2,2] .empty .empty) (.node [10,6,5,3,3,2,2,2,1,1] .empty .empty))))

def degreeTree35_20 : RowTree := (.node [10,6,2,2,2,2,2,2,2,2,2,1] degreeTree35_18 degreeTree35_19)

def degreeTree35_21 : RowTree := (.node [10,7,4,3,2,2,2,2,2,1] (.node [10,6,6,3,3,2,2,1,1,1] (.node [10,6,5,4,4,2,1,1,1,1] (.node [10,6,5,4,3,2,2,1,1,1] (.node [10,6,5,4,2,2,2,2,1,1] .empty .empty) (.node [10,6,5,4,3,3,1,1,1,1] .empty .empty)) (.node [10,6,6,2,2,2,2,2,2,1] (.node [10,6,5,5,2,2,2,1,1,1] .empty .empty) (.node [10,6,6,3,2,2,2,2,1,1] .empty .empty))) (.node [10,7,3,3,3,2,2,2,2,1] (.node [10,6,6,4,2,2,2,1,1,1] (.node [10,6,6,3,3,3,1,1,1,1] .empty .empty) (.node [10,7,3,3,2,2,2,2,2,2] .empty .empty)) (.node [10,7,3,3,3,3,3,1,1,1] (.node [10,7,3,3,3,3,2,2,1,1] .empty .empty) (.node [10,7,4,2,2,2,2,2,2,2] .empty .empty)))) (.node [10,7,6,2,2,2,2,2,1,1] (.node [10,7,4,4,3,2,2,1,1,1] (.node [10,7,4,3,3,3,2,1,1,1] (.node [10,7,4,3,3,2,2,2,1,1] .empty .empty) (.node [10,7,4,4,2,2,2,2,1,1] .empty .empty)) (.node [10,7,5,3,2,2,2,2,1,1] (.node [10,7,5,2,2,2,2,2,2,1] .empty .empty) (.node [10,7,5,3,3,2,2,1,1,1] .empty .empty))) (.node [10,8,4,2,2,2,2,2,2,1] (.node [10,8,3,3,2,2,2,2,2,1] (.node [10,8,3,2,2,2,2,2,2,2] .empty .empty) (.node [10,8,3,3,3,2,2,2,1,1] .empty .empty)) (.node [10,9,2,2,2,2,2,2,2,2] (.node [10,8,4,3,2,2,2,2,1,1] .empty .empty) (.node [10,9,3,2,2,2,2,2,2,1] .empty .empty)))))

def degreeTree35_22 : RowTree := (.node [10,6,5,3,3,3,2,1,1,1] degreeTree35_20 degreeTree35_21)

def degreeTree35_23 : RowTree := (.node [10,5,5,3,2,2,2,2,2,2] degreeTree35_17 degreeTree35_22)

def degreeTree35_24 : RowTree := (.node [10,4,4,2,2,2,2,2,2,2,2,1] degreeTree35_12 degreeTree35_23)

def degreeTree35 : RowTree := degreeTree35_24

end UniversalTensorSquare
end
end

end OAI
