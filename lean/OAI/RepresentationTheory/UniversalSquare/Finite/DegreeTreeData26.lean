import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Tree Data 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeTree26_0 : RowTree := (.node [7,2,2,2,2,2,2,2,2,1,1,1] (.node [7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,2,2,2,2,2,2,1,1,1,1,1,1,1] (.node [7,2,2,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,2,2,2,2,2,2,2,1,1,1,1,1] .empty .empty))) (.node [7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,2,2,2,2,2,2,2,2,2,1] .empty .empty) (.node [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,3,2,2,2,2,1,1,1,1,1,1,1,1] (.node [7,3,2,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,3,2,2,2,2,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_1 : RowTree := (.node [7,3,3,2,2,2,2,2,2,1] (.node [7,3,3,2,2,1,1,1,1,1,1,1,1,1] (.node [7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,2,2,2,2,2,2,2,2] (.node [7,3,2,2,2,2,2,2,2,1,1] .empty .empty) .empty) (.node [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,3,3,2,2,2,2,1,1,1,1,1] (.node [7,3,3,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [7,3,3,2,2,2,2,2,1,1,1] .empty .empty))) (.node [7,3,3,3,2,2,2,1,1,1,1] (.node [7,3,3,3,2,1,1,1,1,1,1,1,1] (.node [7,3,3,3,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,3,3,3,2,2,1,1,1,1,1,1] .empty .empty)) (.node [7,3,3,3,2,2,2,2,2] (.node [7,3,3,3,2,2,2,2,1,1] .empty .empty) (.node [7,3,3,3,3,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_2 : RowTree := (.node [7,3,2,2,2,2,2,2,1,1,1,1] degreeTree26_0 degreeTree26_1)

def degreeTree26_3 : RowTree := (.node [7,4,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,3,3,3,3,2,2] (.node [7,3,3,3,3,3,1,1,1,1] (.node [7,3,3,3,3,2,2,2,1] (.node [7,3,3,3,3,2,2,1,1,1] .empty .empty) .empty) (.node [7,3,3,3,3,3,2,1,1] .empty .empty)) (.node [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,3,3,3,3,3,3,1] .empty .empty) (.node [7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,4,2,2,2,2,2,2,1,1,1] (.node [7,4,2,2,2,2,1,1,1,1,1,1,1] (.node [7,4,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,4,2,2,2,2,2,1,1,1,1,1] .empty .empty)) (.node [7,4,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,4,2,2,2,2,2,2,2,1] .empty .empty) (.node [7,4,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_4 : RowTree := (.node [7,4,3,3,2,2,2,1,1,1] (.node [7,4,3,2,2,2,2,2,2] (.node [7,4,3,2,2,2,2,1,1,1,1] (.node [7,4,3,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [7,4,3,2,2,2,2,2,1,1] .empty .empty)) (.node [7,4,3,3,2,1,1,1,1,1,1,1] (.node [7,4,3,3,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,4,3,3,2,2,1,1,1,1,1] .empty .empty))) (.node [7,4,3,3,3,2,2,1,1] (.node [7,4,3,3,3,1,1,1,1,1,1] (.node [7,4,3,3,2,2,2,2,1] .empty .empty) (.node [7,4,3,3,3,2,1,1,1,1] .empty .empty)) (.node [7,4,3,3,3,3,1,1,1] (.node [7,4,3,3,3,2,2,2] .empty .empty) (.node [7,4,3,3,3,3,2,1] .empty .empty))))

def degreeTree26_5 : RowTree := (.node [7,4,3,2,2,1,1,1,1,1,1,1,1] degreeTree26_3 degreeTree26_4)

def degreeTree26_6 : RowTree := (.node [7,3,3,3,3,2,1,1,1,1,1] degreeTree26_2 degreeTree26_5)

def degreeTree26_7 : RowTree := (.node [7,4,4,3,2,2,1,1,1,1] (.node [7,4,4,2,2,2,2,1,1,1] (.node [7,4,4,2,2,1,1,1,1,1,1,1] (.node [7,4,4,2,1,1,1,1,1,1,1,1,1] (.node [7,4,4,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [7,4,4,2,2,2,1,1,1,1,1] .empty .empty)) (.node [7,4,4,3,1,1,1,1,1,1,1,1] (.node [7,4,4,2,2,2,2,2,1] .empty .empty) (.node [7,4,4,3,2,1,1,1,1,1,1] .empty .empty))) (.node [7,4,4,3,3,2,1,1,1] (.node [7,4,4,3,2,2,2,2] (.node [7,4,4,3,2,2,2,1,1] .empty .empty) (.node [7,4,4,3,3,1,1,1,1,1] .empty .empty)) (.node [7,4,4,3,3,3,1,1] (.node [7,4,4,3,3,2,2,1] .empty .empty) (.node [7,4,4,3,3,3,2] .empty .empty))))

def degreeTree26_8 : RowTree := (.node [7,4,4,4,4,1,1,1] (.node [7,4,4,4,3,1,1,1,1] (.node [7,4,4,4,2,2,1,1,1] (.node [7,4,4,4,2,1,1,1,1,1] .empty .empty) (.node [7,4,4,4,2,2,2,1] .empty .empty)) (.node [7,4,4,4,3,2,2] (.node [7,4,4,4,3,2,1,1] .empty .empty) (.node [7,4,4,4,3,3,1] .empty .empty))) (.node [7,5,2,2,1,1,1,1,1,1,1,1,1,1] (.node [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,4,4,4,4,2,1] .empty .empty) (.node [7,5,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,5,2,2,2,2,1,1,1,1,1,1] (.node [7,5,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,5,2,2,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree26_9 : RowTree := (.node [7,4,4,4,1,1,1,1,1,1,1] degreeTree26_7 degreeTree26_8)

def degreeTree26_10 : RowTree := (.node [7,5,3,3,2,1,1,1,1,1,1] (.node [7,5,3,2,2,2,1,1,1,1,1] (.node [7,5,3,2,1,1,1,1,1,1,1,1,1] (.node [7,5,3,1,1,1,1,1,1,1,1,1,1,1] (.node [7,5,2,2,2,2,2,2,2] .empty .empty) .empty) (.node [7,5,3,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [7,5,3,2,2,2,2,2,1] (.node [7,5,3,2,2,2,2,1,1,1] .empty .empty) (.node [7,5,3,3,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,5,3,3,3,1,1,1,1,1] (.node [7,5,3,3,2,2,2,1,1] (.node [7,5,3,3,2,2,1,1,1,1] .empty .empty) (.node [7,5,3,3,2,2,2,2] .empty .empty)) (.node [7,5,3,3,3,2,2,1] (.node [7,5,3,3,3,2,1,1,1] .empty .empty) (.node [7,5,3,3,3,3,1,1] .empty .empty))))

def degreeTree26_11 : RowTree := (.node [7,5,4,3,2,1,1,1,1,1] (.node [7,5,4,2,2,2,1,1,1,1] (.node [7,5,4,2,1,1,1,1,1,1,1,1] (.node [7,5,4,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,5,4,2,2,1,1,1,1,1,1] .empty .empty)) (.node [7,5,4,2,2,2,2,2] (.node [7,5,4,2,2,2,2,1,1] .empty .empty) (.node [7,5,4,3,1,1,1,1,1,1,1] .empty .empty))) (.node [7,5,4,3,3,2,1,1] (.node [7,5,4,3,2,2,2,1] (.node [7,5,4,3,2,2,1,1,1] .empty .empty) (.node [7,5,4,3,3,1,1,1,1] .empty .empty)) (.node [7,5,4,3,3,3,1] (.node [7,5,4,3,3,2,2] .empty .empty) (.node [7,5,4,4,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_12 : RowTree := (.node [7,5,3,3,3,3,2] degreeTree26_10 degreeTree26_11)

def degreeTree26_13 : RowTree := (.node [7,5,2,2,2,2,2,2,1,1] degreeTree26_9 degreeTree26_12)

def degreeTree26_14 : RowTree := (.node [7,4,3,3,3,3,3] degreeTree26_6 degreeTree26_13)

def degreeTree26_15 : RowTree := (.node [7,5,5,2,2,2,1,1,1] (.node [7,5,4,4,4,1,1] (.node [7,5,4,4,3,1,1,1] (.node [7,5,4,4,2,2,2] (.node [7,5,4,4,2,2,1,1] .empty .empty) .empty) (.node [7,5,4,4,3,2,1] .empty .empty)) (.node [7,5,5,2,1,1,1,1,1,1,1] (.node [7,5,5,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,5,5,2,2,1,1,1,1,1] .empty .empty))) (.node [7,5,5,3,2,2,1,1] (.node [7,5,5,3,1,1,1,1,1,1] (.node [7,5,5,2,2,2,2,1] .empty .empty) (.node [7,5,5,3,2,1,1,1,1] .empty .empty)) (.node [7,5,5,3,3,1,1,1] (.node [7,5,5,3,2,2,2] .empty .empty) (.node [7,5,5,3,3,2,1] .empty .empty))))

def degreeTree26_16 : RowTree := (.node [7,6,2,2,2,1,1,1,1,1,1,1] (.node [7,5,5,5,1,1,1,1] (.node [7,5,5,4,2,2,1] (.node [7,5,5,4,2,1,1,1] .empty .empty) (.node [7,5,5,4,3,1,1] .empty .empty)) (.node [7,6,2,1,1,1,1,1,1,1,1,1,1,1] (.node [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,6,2,2,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,6,3,1,1,1,1,1,1,1,1,1,1] (.node [7,6,2,2,2,2,2,1,1,1] (.node [7,6,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [7,6,2,2,2,2,2,2,1] .empty .empty)) (.node [7,6,3,2,2,1,1,1,1,1,1] (.node [7,6,3,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,6,3,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree26_17 : RowTree := (.node [7,5,5,4,1,1,1,1,1] degreeTree26_15 degreeTree26_16)

def degreeTree26_18 : RowTree := (.node [7,6,3,3,3,3,1] (.node [7,6,3,3,2,2,2,1] (.node [7,6,3,3,2,1,1,1,1,1] (.node [7,6,3,3,1,1,1,1,1,1,1] (.node [7,6,3,2,2,2,2,2] .empty .empty) .empty) (.node [7,6,3,3,2,2,1,1,1] .empty .empty)) (.node [7,6,3,3,3,2,1,1] (.node [7,6,3,3,3,1,1,1,1] .empty .empty) (.node [7,6,3,3,3,2,2] .empty .empty))) (.node [7,6,4,2,2,2,1,1,1] (.node [7,6,4,2,1,1,1,1,1,1,1] (.node [7,6,4,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,6,4,2,2,1,1,1,1,1] .empty .empty)) (.node [7,6,4,3,1,1,1,1,1,1] (.node [7,6,4,2,2,2,2,1] .empty .empty) (.node [7,6,4,3,2,1,1,1,1] .empty .empty))))

def degreeTree26_19 : RowTree := (.node [7,6,5,2,1,1,1,1,1,1] (.node [7,6,4,4,1,1,1,1,1] (.node [7,6,4,3,3,1,1,1] (.node [7,6,4,3,2,2,2] .empty .empty) (.node [7,6,4,3,3,2,1] .empty .empty)) (.node [7,6,4,4,2,2,1] (.node [7,6,4,4,2,1,1,1] .empty .empty) (.node [7,6,5,1,1,1,1,1,1,1,1] .empty .empty))) (.node [7,6,5,3,1,1,1,1,1] (.node [7,6,5,2,2,2,1,1] (.node [7,6,5,2,2,1,1,1,1] .empty .empty) (.node [7,6,5,2,2,2,2] .empty .empty)) (.node [7,6,5,4,1,1,1,1] (.node [7,6,5,3,2,1,1,1] .empty .empty) (.node [7,6,6,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_20 : RowTree := (.node [7,6,4,3,2,2,1,1] degreeTree26_18 degreeTree26_19)

def degreeTree26_21 : RowTree := (.node [7,6,3,2,2,2,2,1,1] degreeTree26_17 degreeTree26_20)

def degreeTree26_22 : RowTree := (.node [7,7,2,2,2,2,2,2] (.node [7,7,2,2,1,1,1,1,1,1,1,1] (.node [7,7,1,1,1,1,1,1,1,1,1,1,1,1] (.node [7,6,6,3,1,1,1,1] (.node [7,6,6,2,2,1,1,1] .empty .empty) .empty) (.node [7,7,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,7,2,2,2,2,1,1,1,1] (.node [7,7,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [7,7,2,2,2,2,2,1,1] .empty .empty))) (.node [7,7,3,2,2,2,1,1,1] (.node [7,7,3,2,1,1,1,1,1,1,1] (.node [7,7,3,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [7,7,3,2,2,1,1,1,1,1] .empty .empty)) (.node [7,7,3,3,1,1,1,1,1,1] (.node [7,7,3,2,2,2,2,1] .empty .empty) (.node [7,7,3,3,2,1,1,1,1] .empty .empty))))

def degreeTree26_23 : RowTree := (.node [7,7,4,3,2,1,1,1] (.node [7,7,4,2,1,1,1,1,1,1] (.node [7,7,3,3,3,1,1,1] (.node [7,7,3,3,2,2,2] .empty .empty) (.node [7,7,4,1,1,1,1,1,1,1,1] .empty .empty)) (.node [7,7,4,2,2,2,1,1] (.node [7,7,4,2,2,1,1,1,1] .empty .empty) (.node [7,7,4,3,1,1,1,1,1] .empty .empty))) (.node [7,7,5,2,2,1,1,1] (.node [7,7,5,1,1,1,1,1,1,1] (.node [7,7,4,4,1,1,1,1] .empty .empty) (.node [7,7,5,2,1,1,1,1,1] .empty .empty)) (.node [7,7,6,1,1,1,1,1,1] (.node [7,7,5,3,1,1,1,1] .empty .empty) (.node [7,7,6,2,1,1,1,1] .empty .empty))))

def degreeTree26_24 : RowTree := (.node [7,7,3,3,2,2,1,1] degreeTree26_22 degreeTree26_23)

def degreeTree26_25 : RowTree := (.node [8,2,2,2,2,2,2,2,2,1,1] (.node [8,2,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,2,2,2,2,2,2,1,1,1,1,1,1] (.node [8,2,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,2,2,2,2,2,2,2,1,1,1,1] .empty .empty))) (.node [8,3,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,2,2,2,2,2,2,2,2,2] .empty .empty) (.node [8,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,3,2,2,2,2,1,1,1,1,1,1,1] (.node [8,3,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,3,2,2,2,2,2,1,1,1,1,1] .empty .empty))))

def degreeTree26_26 : RowTree := (.node [8,3,3,2,2,2,2,2,2] (.node [8,3,3,2,2,1,1,1,1,1,1,1,1] (.node [8,3,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,3,2,2,2,2,2,2,2,1] .empty .empty) (.node [8,3,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,3,3,2,2,2,2,1,1,1,1] (.node [8,3,3,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [8,3,3,2,2,2,2,2,1,1] .empty .empty))) (.node [8,3,3,3,2,2,2,1,1,1] (.node [8,3,3,3,2,1,1,1,1,1,1,1] (.node [8,3,3,3,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,3,3,3,2,2,1,1,1,1,1] .empty .empty)) (.node [8,3,3,3,3,1,1,1,1,1,1] (.node [8,3,3,3,2,2,2,2,1] .empty .empty) (.node [8,3,3,3,3,2,1,1,1,1] .empty .empty))))

def degreeTree26_27 : RowTree := (.node [8,3,2,2,2,2,2,2,1,1,1] degreeTree26_25 degreeTree26_26)

def degreeTree26_28 : RowTree := (.node [7,7,7,1,1,1,1,1] degreeTree26_24 degreeTree26_27)

def degreeTree26_29 : RowTree := (.node [7,6,6,2,1,1,1,1,1] degreeTree26_21 degreeTree26_28)

def degreeTree26_30 : RowTree := (.node [7,5,4,4,2,1,1,1,1] degreeTree26_14 degreeTree26_29)

def degreeTree26_31 : RowTree := (.node [8,4,2,2,2,2,2,1,1,1,1] (.node [8,4,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,3,3,3,3,3,2,1] (.node [8,3,3,3,3,3,1,1,1] (.node [8,3,3,3,3,2,2,2] .empty .empty) .empty) (.node [8,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,4,2,2,2,1,1,1,1,1,1,1,1] (.node [8,4,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,2,2,2,2,1,1,1,1,1,1] .empty .empty))) (.node [8,4,3,2,1,1,1,1,1,1,1,1,1] (.node [8,4,2,2,2,2,2,2,2] (.node [8,4,2,2,2,2,2,2,1,1] .empty .empty) (.node [8,4,3,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,4,3,2,2,2,1,1,1,1,1] (.node [8,4,3,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,3,2,2,2,2,1,1,1] .empty .empty))))

def degreeTree26_32 : RowTree := (.node [8,4,3,3,3,2,2,1] (.node [8,4,3,3,2,2,2,1,1] (.node [8,4,3,3,2,1,1,1,1,1,1] (.node [8,4,3,3,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,4,3,3,2,2,1,1,1,1] .empty .empty)) (.node [8,4,3,3,3,1,1,1,1,1] (.node [8,4,3,3,2,2,2,2] .empty .empty) (.node [8,4,3,3,3,2,1,1,1] .empty .empty))) (.node [8,4,4,2,2,1,1,1,1,1,1] (.node [8,4,4,1,1,1,1,1,1,1,1,1,1] (.node [8,4,3,3,3,3,1,1] .empty .empty) (.node [8,4,4,2,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,4,4,2,2,2,2,1,1] (.node [8,4,4,2,2,2,1,1,1,1] .empty .empty) (.node [8,4,4,2,2,2,2,2] .empty .empty))))

def degreeTree26_33 : RowTree := (.node [8,4,3,2,2,2,2,2,1] degreeTree26_31 degreeTree26_32)

def degreeTree26_34 : RowTree := (.node [8,4,4,4,3,1,1,1] (.node [8,4,4,3,3,2,1,1] (.node [8,4,4,3,2,2,2,1] (.node [8,4,4,3,2,2,1,1,1] (.node [8,4,4,3,2,1,1,1,1,1] .empty .empty) .empty) (.node [8,4,4,3,3,1,1,1,1] .empty .empty)) (.node [8,4,4,4,2,1,1,1,1] (.node [8,4,4,4,1,1,1,1,1,1] .empty .empty) (.node [8,4,4,4,2,2,1,1] .empty .empty))) (.node [8,5,2,2,2,1,1,1,1,1,1,1] (.node [8,5,2,1,1,1,1,1,1,1,1,1,1,1] (.node [8,5,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,5,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,5,2,2,2,2,2,1,1,1] (.node [8,5,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [8,5,2,2,2,2,2,2,1] .empty .empty))))

def degreeTree26_35 : RowTree := (.node [8,5,3,3,2,2,1,1,1] (.node [8,5,3,2,2,2,2,1,1] (.node [8,5,3,2,2,1,1,1,1,1,1] (.node [8,5,3,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,5,3,2,2,2,1,1,1,1] .empty .empty)) (.node [8,5,3,3,1,1,1,1,1,1,1] (.node [8,5,3,2,2,2,2,2] .empty .empty) (.node [8,5,3,3,2,1,1,1,1,1] .empty .empty))) (.node [8,5,4,1,1,1,1,1,1,1,1,1] (.node [8,5,3,3,3,1,1,1,1] (.node [8,5,3,3,2,2,2,1] .empty .empty) (.node [8,5,3,3,3,2,1,1] .empty .empty)) (.node [8,5,4,2,2,1,1,1,1,1] (.node [8,5,4,2,1,1,1,1,1,1,1] .empty .empty) (.node [8,5,4,2,2,2,1,1,1] .empty .empty))))

def degreeTree26_36 : RowTree := (.node [8,5,3,1,1,1,1,1,1,1,1,1,1] degreeTree26_34 degreeTree26_35)

def degreeTree26_37 : RowTree := (.node [8,4,4,3,1,1,1,1,1,1,1] degreeTree26_33 degreeTree26_36)

def degreeTree26_38 : RowTree := (.node [8,5,5,2,2,1,1,1,1] (.node [8,5,4,4,1,1,1,1,1] (.node [8,5,4,3,2,2,1,1] (.node [8,5,4,3,2,1,1,1,1] (.node [8,5,4,3,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,5,4,3,3,1,1,1] .empty .empty)) (.node [8,5,5,1,1,1,1,1,1,1,1] (.node [8,5,4,4,2,1,1,1] .empty .empty) (.node [8,5,5,2,1,1,1,1,1,1] .empty .empty))) (.node [8,6,2,1,1,1,1,1,1,1,1,1,1] (.node [8,5,5,3,1,1,1,1,1] (.node [8,5,5,2,2,2,1,1] .empty .empty) (.node [8,6,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [8,6,2,2,2,1,1,1,1,1,1] (.node [8,6,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,6,2,2,2,2,1,1,1,1] .empty .empty))))

def degreeTree26_39 : RowTree := (.node [8,6,3,3,2,1,1,1,1] (.node [8,6,3,2,2,1,1,1,1,1] (.node [8,6,3,1,1,1,1,1,1,1,1,1] (.node [8,6,2,2,2,2,2,2] .empty .empty) (.node [8,6,3,2,1,1,1,1,1,1,1] .empty .empty)) (.node [8,6,3,2,2,2,2,1] (.node [8,6,3,2,2,2,1,1,1] .empty .empty) (.node [8,6,3,3,1,1,1,1,1,1] .empty .empty))) (.node [8,6,4,2,2,1,1,1,1] (.node [8,6,4,1,1,1,1,1,1,1,1] (.node [8,6,3,3,2,2,1,1] .empty .empty) (.node [8,6,4,2,1,1,1,1,1,1] .empty .empty)) (.node [8,6,5,1,1,1,1,1,1,1] (.node [8,6,4,3,1,1,1,1,1] .empty .empty) (.node [8,6,5,2,1,1,1,1,1] .empty .empty))))

def degreeTree26_40 : RowTree := (.node [8,6,2,2,2,2,2,1,1] degreeTree26_38 degreeTree26_39)

def degreeTree26_41 : RowTree := (.node [8,7,3,2,2,1,1,1,1] (.node [8,7,2,2,2,2,1,1,1] (.node [8,7,2,2,1,1,1,1,1,1,1] (.node [8,7,2,1,1,1,1,1,1,1,1,1] (.node [8,7,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [8,7,2,2,2,1,1,1,1,1] .empty .empty)) (.node [8,7,3,1,1,1,1,1,1,1,1] (.node [8,7,2,2,2,2,2,1] .empty .empty) (.node [8,7,3,2,1,1,1,1,1,1] .empty .empty))) (.node [8,7,5,1,1,1,1,1,1] (.node [8,7,4,1,1,1,1,1,1,1] (.node [8,7,3,3,1,1,1,1,1] .empty .empty) (.node [8,7,4,2,1,1,1,1,1] .empty .empty)) (.node [8,8,2,1,1,1,1,1,1,1,1] (.node [8,8,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [8,8,2,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_42 : RowTree := (.node [9,2,2,2,2,1,1,1,1,1,1,1,1,1] (.node [9,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [8,8,3,2,1,1,1,1,1] (.node [8,8,3,1,1,1,1,1,1,1] .empty .empty) (.node [8,8,4,1,1,1,1,1,1] .empty .empty)) (.node [9,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,2,2,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [9,2,2,2,2,2,2,2,2,1] (.node [9,2,2,2,2,2,2,1,1,1,1,1] (.node [9,2,2,2,2,2,1,1,1,1,1,1,1] .empty .empty) (.node [9,2,2,2,2,2,2,2,1,1,1] .empty .empty)) (.node [9,3,2,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,3,2,2,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_43 : RowTree := (.node [8,8,2,2,2,1,1,1,1] degreeTree26_41 degreeTree26_42)

def degreeTree26_44 : RowTree := (.node [8,6,6,1,1,1,1,1,1] degreeTree26_40 degreeTree26_43)

def degreeTree26_45 : RowTree := (.node [8,5,4,2,2,2,2,1] degreeTree26_37 degreeTree26_44)

def degreeTree26_46 : RowTree := (.node [9,3,3,2,2,2,2,1,1,1] (.node [9,3,3,1,1,1,1,1,1,1,1,1,1,1] (.node [9,3,2,2,2,2,2,2,1,1] (.node [9,3,2,2,2,2,2,1,1,1,1] (.node [9,3,2,2,2,2,1,1,1,1,1,1] .empty .empty) .empty) (.node [9,3,2,2,2,2,2,2,2] .empty .empty)) (.node [9,3,3,2,2,1,1,1,1,1,1,1] (.node [9,3,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,3,3,2,2,2,1,1,1,1,1] .empty .empty))) (.node [9,3,3,3,2,2,1,1,1,1] (.node [9,3,3,3,1,1,1,1,1,1,1,1] (.node [9,3,3,2,2,2,2,2,1] .empty .empty) (.node [9,3,3,3,2,1,1,1,1,1,1] .empty .empty)) (.node [9,3,3,3,3,1,1,1,1,1] (.node [9,3,3,3,2,2,2,1,1] .empty .empty) (.node [9,3,3,3,3,2,1,1,1] .empty .empty))))

def degreeTree26_47 : RowTree := (.node [9,4,3,2,1,1,1,1,1,1,1,1] (.node [9,4,2,2,2,2,1,1,1,1,1] (.node [9,4,2,2,1,1,1,1,1,1,1,1,1] (.node [9,4,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,4,2,2,2,1,1,1,1,1,1,1] .empty .empty)) (.node [9,4,2,2,2,2,2,2,1] (.node [9,4,2,2,2,2,2,1,1,1] .empty .empty) (.node [9,4,3,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [9,4,3,3,1,1,1,1,1,1,1] (.node [9,4,3,2,2,2,1,1,1,1] (.node [9,4,3,2,2,1,1,1,1,1,1] .empty .empty) (.node [9,4,3,2,2,2,2,1,1] .empty .empty)) (.node [9,4,3,3,2,2,1,1,1] (.node [9,4,3,3,2,1,1,1,1,1] .empty .empty) (.node [9,4,3,3,3,1,1,1,1] .empty .empty))))

def degreeTree26_48 : RowTree := (.node [9,4,1,1,1,1,1,1,1,1,1,1,1,1,1] degreeTree26_46 degreeTree26_47)

def degreeTree26_49 : RowTree := (.node [9,5,2,2,1,1,1,1,1,1,1,1] (.node [9,4,4,3,2,1,1,1,1] (.node [9,4,4,2,2,2,1,1,1] (.node [9,4,4,2,2,1,1,1,1,1] (.node [9,4,4,2,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [9,4,4,3,1,1,1,1,1,1] .empty .empty)) (.node [9,5,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,4,4,4,1,1,1,1,1] .empty .empty) (.node [9,5,2,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [9,5,3,1,1,1,1,1,1,1,1,1] (.node [9,5,2,2,2,2,1,1,1,1] (.node [9,5,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [9,5,2,2,2,2,2,1,1] .empty .empty)) (.node [9,5,3,2,2,1,1,1,1,1] (.node [9,5,3,2,1,1,1,1,1,1,1] .empty .empty) (.node [9,5,3,2,2,2,1,1,1] .empty .empty))))

def degreeTree26_50 : RowTree := (.node [9,6,2,2,2,1,1,1,1,1] (.node [9,5,5,1,1,1,1,1,1,1] (.node [9,5,4,1,1,1,1,1,1,1,1] (.node [9,5,3,3,2,1,1,1,1] .empty .empty) (.node [9,5,4,2,1,1,1,1,1,1] .empty .empty)) (.node [9,6,2,1,1,1,1,1,1,1,1,1] (.node [9,6,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,6,2,2,1,1,1,1,1,1,1] .empty .empty))) (.node [9,6,4,1,1,1,1,1,1,1] (.node [9,6,3,1,1,1,1,1,1,1,1] (.node [9,6,2,2,2,2,1,1,1] .empty .empty) (.node [9,6,3,2,1,1,1,1,1,1] .empty .empty)) (.node [9,7,2,1,1,1,1,1,1,1,1] (.node [9,7,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [9,7,2,2,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_51 : RowTree := (.node [9,5,3,3,1,1,1,1,1,1] degreeTree26_49 degreeTree26_50)

def degreeTree26_52 : RowTree := (.node [9,4,4,1,1,1,1,1,1,1,1,1] degreeTree26_48 degreeTree26_51)

def degreeTree26_53 : RowTree := (.node [10,2,2,2,2,2,1,1,1,1,1,1] (.node [10,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [9,9,1,1,1,1,1,1,1,1] (.node [9,8,2,1,1,1,1,1,1,1] (.node [9,8,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [10,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,2,2,2,1,1,1,1,1,1,1,1,1,1] (.node [10,2,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,2,2,2,2,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,3,2,1,1,1,1,1,1,1,1,1,1,1] (.node [10,2,2,2,2,2,2,2,1,1] (.node [10,2,2,2,2,2,2,1,1,1,1] .empty .empty) (.node [10,3,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [10,3,2,2,2,1,1,1,1,1,1,1] (.node [10,3,2,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,3,2,2,2,2,1,1,1,1,1] .empty .empty))))

def degreeTree26_54 : RowTree := (.node [10,4,2,1,1,1,1,1,1,1,1,1,1] (.node [10,3,3,2,2,2,1,1,1,1] (.node [10,3,3,2,1,1,1,1,1,1,1,1] (.node [10,3,3,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,3,3,2,2,1,1,1,1,1,1] .empty .empty)) (.node [10,3,3,3,2,1,1,1,1,1] (.node [10,3,3,3,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [10,4,3,1,1,1,1,1,1,1,1,1] (.node [10,4,2,2,2,1,1,1,1,1,1] (.node [10,4,2,2,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,2,2,2,2,1,1,1,1] .empty .empty)) (.node [10,4,3,2,2,1,1,1,1,1] (.node [10,4,3,2,1,1,1,1,1,1,1] .empty .empty) (.node [10,4,3,3,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_55 : RowTree := (.node [10,3,2,2,2,2,2,1,1,1] degreeTree26_53 degreeTree26_54)

def degreeTree26_56 : RowTree := (.node [11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [10,5,3,1,1,1,1,1,1,1,1] (.node [10,5,2,2,1,1,1,1,1,1,1] (.node [10,5,2,1,1,1,1,1,1,1,1,1] (.node [10,5,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) .empty) (.node [10,5,2,2,2,1,1,1,1,1] .empty .empty)) (.node [10,6,2,1,1,1,1,1,1,1,1] (.node [10,6,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [10,7,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [11,2,2,2,2,1,1,1,1,1,1,1] (.node [11,2,2,1,1,1,1,1,1,1,1,1,1,1] (.node [11,2,1,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [11,2,2,2,1,1,1,1,1,1,1,1,1] .empty .empty)) (.node [11,3,1,1,1,1,1,1,1,1,1,1,1,1] (.node [11,2,2,2,2,2,1,1,1,1,1] .empty .empty) (.node [11,3,2,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_57 : RowTree := (.node [12,1,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [11,4,1,1,1,1,1,1,1,1,1,1,1] (.node [11,3,3,1,1,1,1,1,1,1,1,1] (.node [11,3,2,2,2,1,1,1,1,1,1] .empty .empty) (.node [11,3,3,2,1,1,1,1,1,1,1] .empty .empty)) (.node [11,4,2,2,1,1,1,1,1,1,1] (.node [11,4,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [11,5,1,1,1,1,1,1,1,1,1,1] .empty .empty))) (.node [12,3,1,1,1,1,1,1,1,1,1,1,1] (.node [12,2,2,1,1,1,1,1,1,1,1,1,1] (.node [12,2,1,1,1,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [12,2,2,2,1,1,1,1,1,1,1,1] .empty .empty)) (.node [13,1,1,1,1,1,1,1,1,1,1,1,1,1] (.node [12,3,2,1,1,1,1,1,1,1,1,1] .empty .empty) (.node [13,2,1,1,1,1,1,1,1,1,1,1,1] .empty .empty))))

def degreeTree26_58 : RowTree := (.node [11,3,2,2,1,1,1,1,1,1,1,1] degreeTree26_56 degreeTree26_57)

def degreeTree26_59 : RowTree := (.node [10,4,4,1,1,1,1,1,1,1,1] degreeTree26_55 degreeTree26_58)

def degreeTree26_60 : RowTree := (.node [9,7,3,1,1,1,1,1,1,1] degreeTree26_52 degreeTree26_59)

def degreeTree26_61 : RowTree := (.node [9,3,2,2,2,1,1,1,1,1,1,1,1] degreeTree26_45 degreeTree26_60)

def degreeTree26_62 : RowTree := (.node [8,3,3,3,3,2,2,1,1] degreeTree26_30 degreeTree26_61)

def degreeTree26 : RowTree := degreeTree26_62

end UniversalTensorSquare
end
end

end OAI
