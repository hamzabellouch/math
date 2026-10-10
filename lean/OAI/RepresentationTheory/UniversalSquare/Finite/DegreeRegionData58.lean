import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 58. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion58_0 : PrefixRegion := ([(1,14),(3,21)], [(1,14),(3,29),(7,46)])
def degreeRegion58_1 : PrefixRegion := ([(1,14),(3,21)], [(1,14),(3,29),(8,49)])
def degreeRegion58_2 : PrefixRegion := ([(1,14),(3,29),(5,35)], [(1,14),(3,29),(5,35)])
def degreeRegion58_3 : PrefixRegion := ([(1,14),(3,29),(5,35)], [(1,14),(3,29),(6,42)])
def degreeRegion58_4 : PrefixRegion := ([(1,14),(3,29),(5,35)], [(1,14),(3,29),(7,46)])
def degreeRegion58_5 : PrefixRegion := ([(1,14),(3,29),(5,35)], [(1,14),(3,29),(8,49)])
def degreeRegion58_6 : PrefixRegion := ([(1,14),(3,29),(5,35)], [(1,14),(3,29),(9,52)])
def degreeRegion58_7 : PrefixRegion := ([(1,14),(3,29),(5,35)], [(1,14),(3,29),(10,55)])
def degreeRegion58_8 : PrefixRegion := ([(1,14),(3,29),(6,42)], [(1,14),(3,29),(5,35)])
def degreeRegion58_9 : PrefixRegion := ([(1,14),(3,29),(6,42)], [(1,14),(3,29),(6,42)])
def degreeRegion58_10 : PrefixRegion := ([(1,14),(3,29),(6,42)], [(1,14),(3,29),(7,46)])
def degreeRegion58_11 : PrefixRegion := ([(1,14),(3,29),(6,42)], [(1,14),(3,29),(8,49)])
def degreeRegion58_12 : PrefixRegion := ([(1,14),(3,29),(6,42)], [(1,14),(3,29),(9,52)])
def degreeRegion58_13 : PrefixRegion := ([(1,14),(3,29),(6,42)], [(1,14),(3,29),(10,55)])
def degreeRegion58_14 : PrefixRegion := ([(1,14),(3,29),(6,42)], [(1,14),(3,29),(11,57)])
def degreeRegion58_15 : PrefixRegion := ([(1,14),(3,29),(6,42)], [(1,14),(4,28)])
def degreeRegion58_16 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,21)])
def degreeRegion58_17 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,29),(5,35)])
def degreeRegion58_18 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,29),(6,42)])
def degreeRegion58_19 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,29),(7,46)])
def degreeRegion58_20 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,29),(8,49)])
def degreeRegion58_21 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,29),(9,52)])
def degreeRegion58_22 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,29),(10,55)])
def degreeRegion58_23 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(3,29),(11,57)])
def degreeRegion58_24 : PrefixRegion := ([(1,14),(3,29),(7,46)], [(1,14),(4,28)])
def degreeRegion58_25 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,21)])
def degreeRegion58_26 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(5,35)])
def degreeRegion58_27 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(6,42)])
def degreeRegion58_28 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(7,46)])
def degreeRegion58_29 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(8,49)])
def degreeRegion58_30 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(9,52)])
def degreeRegion58_31 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(10,55)])
def degreeRegion58_32 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(3,29),(11,57)])
def degreeRegion58_33 : PrefixRegion := ([(1,14),(3,29),(8,49)], [(1,14),(4,28)])
def degreeRegion58_34 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(5,35)])
def degreeRegion58_35 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(6,42)])
def degreeRegion58_36 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(7,46)])
def degreeRegion58_37 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(8,49)])
def degreeRegion58_38 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(9,52)])
def degreeRegion58_39 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(10,55)])
def degreeRegion58_40 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(3,29),(11,57)])
def degreeRegion58_41 : PrefixRegion := ([(1,14),(3,29),(9,52)], [(1,14),(4,28)])
def degreeRegion58_42 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(5,35)])
def degreeRegion58_43 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(6,42)])
def degreeRegion58_44 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(7,46)])
def degreeRegion58_45 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(8,49)])
def degreeRegion58_46 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(9,52)])
def degreeRegion58_47 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(10,55)])
def degreeRegion58_48 : PrefixRegion := ([(1,14),(3,29),(10,55)], [(1,14),(3,29),(11,57)])
def degreeRegion58_49 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(6,42)])
def degreeRegion58_50 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(7,46)])
def degreeRegion58_51 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(8,49)])
def degreeRegion58_52 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(9,52)])
def degreeRegion58_53 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(10,55)])
def degreeRegion58_54 : PrefixRegion := ([(1,14),(3,29),(11,57)], [(1,14),(3,29),(11,57)])
def degreeRegion58_55 : PrefixRegion := ([(1,14),(4,28)], [(1,14),(3,29),(6,42)])
def degreeRegion58_56 : PrefixRegion := ([(1,14),(4,28)], [(1,14),(3,29),(7,46)])
def degreeRegion58_57 : PrefixRegion := ([(1,14),(4,28)], [(1,14),(3,29),(8,49)])
def degreeRegion58_58 : PrefixRegion := ([(1,14),(4,28)], [(1,14),(3,29),(9,52)])
def degreeRegion58_59 : PrefixRegion := ([(1,24),(10,55)], [(2,14),(3,29),(7,34)])
def degreeRegion58_60 : PrefixRegion := ([(1,24),(11,57)], [(2,14),(3,29),(7,34)])
def degreeRegion58_61 : PrefixRegion := ([(2,14),(3,29),(7,34)], [(1,24),(10,55)])
def degreeRegion58_62 : PrefixRegion := ([(2,14),(3,29),(7,34)], [(1,24),(11,57)])

def degreeRegions58 : List PrefixRegion := [degreeRegion58_0,degreeRegion58_1,degreeRegion58_2,degreeRegion58_3,degreeRegion58_4,degreeRegion58_5,degreeRegion58_6,degreeRegion58_7,degreeRegion58_8,degreeRegion58_9,degreeRegion58_10,degreeRegion58_11,degreeRegion58_12,degreeRegion58_13,degreeRegion58_14,degreeRegion58_15,degreeRegion58_16,degreeRegion58_17,degreeRegion58_18,degreeRegion58_19,degreeRegion58_20,degreeRegion58_21,degreeRegion58_22,degreeRegion58_23,degreeRegion58_24,degreeRegion58_25,degreeRegion58_26,degreeRegion58_27,degreeRegion58_28,degreeRegion58_29,degreeRegion58_30,degreeRegion58_31,degreeRegion58_32,degreeRegion58_33,degreeRegion58_34,degreeRegion58_35,degreeRegion58_36,degreeRegion58_37,degreeRegion58_38,degreeRegion58_39,degreeRegion58_40,degreeRegion58_41,degreeRegion58_42,degreeRegion58_43,degreeRegion58_44,degreeRegion58_45,degreeRegion58_46,degreeRegion58_47,degreeRegion58_48,degreeRegion58_49,degreeRegion58_50,degreeRegion58_51,degreeRegion58_52,degreeRegion58_53,degreeRegion58_54,degreeRegion58_55,degreeRegion58_56,degreeRegion58_57,degreeRegion58_58,degreeRegion58_59,degreeRegion58_60,degreeRegion58_61,degreeRegion58_62]

end UniversalTensorSquare
end
end

end OAI
