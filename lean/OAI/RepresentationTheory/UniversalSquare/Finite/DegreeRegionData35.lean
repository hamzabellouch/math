import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 35. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion35_0 : PrefixRegion := ([(1,10),(3,15)], [(1,15),(6,30)])
def degreeRegion35_1 : PrefixRegion := ([(1,10),(3,15)], [(1,15),(7,34)])
def degreeRegion35_2 : PrefixRegion := ([(1,10),(3,18),(4,20)], [(1,15),(5,25)])
def degreeRegion35_3 : PrefixRegion := ([(1,10),(3,18),(4,20)], [(1,15),(6,30)])
def degreeRegion35_4 : PrefixRegion := ([(1,10),(3,18),(4,20)], [(1,15),(7,34)])
def degreeRegion35_5 : PrefixRegion := ([(1,10),(3,18),(5,25)], [(1,15),(5,25)])
def degreeRegion35_6 : PrefixRegion := ([(1,10),(3,18),(5,25)], [(1,15),(6,30)])
def degreeRegion35_7 : PrefixRegion := ([(1,10),(3,18),(5,25)], [(1,15),(7,34)])
def degreeRegion35_8 : PrefixRegion := ([(1,10),(3,18),(6,30)], [(1,15),(5,25)])
def degreeRegion35_9 : PrefixRegion := ([(1,10),(3,18),(6,30)], [(1,15),(6,30)])
def degreeRegion35_10 : PrefixRegion := ([(1,10),(3,18),(6,30)], [(1,15),(7,34)])
def degreeRegion35_11 : PrefixRegion := ([(1,10),(3,18),(7,34)], [(1,15),(5,25)])
def degreeRegion35_12 : PrefixRegion := ([(1,10),(3,18),(7,34)], [(1,15),(6,30)])
def degreeRegion35_13 : PrefixRegion := ([(1,10),(3,18),(7,34)], [(1,15),(7,34)])
def degreeRegion35_14 : PrefixRegion := ([(1,10),(4,20)], [(1,10),(5,25)])
def degreeRegion35_15 : PrefixRegion := ([(1,10),(4,20)], [(1,10),(6,30)])
def degreeRegion35_16 : PrefixRegion := ([(1,10),(4,20)], [(1,10),(7,34)])
def degreeRegion35_17 : PrefixRegion := ([(1,10),(5,25)], [(1,10),(4,20)])
def degreeRegion35_18 : PrefixRegion := ([(1,10),(5,25)], [(1,10),(5,25)])
def degreeRegion35_19 : PrefixRegion := ([(1,10),(5,25)], [(1,10),(6,30)])
def degreeRegion35_20 : PrefixRegion := ([(1,10),(5,25)], [(1,10),(7,34)])
def degreeRegion35_21 : PrefixRegion := ([(1,10),(6,30)], [(1,10),(4,20)])
def degreeRegion35_22 : PrefixRegion := ([(1,10),(6,30)], [(1,10),(5,25)])
def degreeRegion35_23 : PrefixRegion := ([(1,10),(6,30)], [(1,10),(6,30)])
def degreeRegion35_24 : PrefixRegion := ([(1,10),(6,30)], [(1,10),(7,34)])
def degreeRegion35_25 : PrefixRegion := ([(1,10),(7,34)], [(1,10),(4,20)])
def degreeRegion35_26 : PrefixRegion := ([(1,10),(7,34)], [(1,10),(5,25)])
def degreeRegion35_27 : PrefixRegion := ([(1,10),(7,34)], [(1,10),(6,30)])
def degreeRegion35_28 : PrefixRegion := ([(1,10),(7,34)], [(1,10),(7,34)])
def degreeRegion35_29 : PrefixRegion := ([(1,15),(3,18),(5,25)], [(1,15),(3,18),(5,25)])
def degreeRegion35_30 : PrefixRegion := ([(1,15),(5,25)], [(1,10),(3,18),(4,20)])
def degreeRegion35_31 : PrefixRegion := ([(1,15),(5,25)], [(1,10),(3,18),(5,25)])
def degreeRegion35_32 : PrefixRegion := ([(1,15),(5,25)], [(1,10),(3,18),(6,30)])
def degreeRegion35_33 : PrefixRegion := ([(1,15),(5,25)], [(1,10),(3,18),(7,34)])
def degreeRegion35_34 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,15)])
def degreeRegion35_35 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,18),(4,20)])
def degreeRegion35_36 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,18),(5,25)])
def degreeRegion35_37 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,18),(6,30)])
def degreeRegion35_38 : PrefixRegion := ([(1,15),(6,30)], [(1,10),(3,18),(7,34)])
def degreeRegion35_39 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,15)])
def degreeRegion35_40 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,18),(4,20)])
def degreeRegion35_41 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,18),(5,25)])
def degreeRegion35_42 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,18),(6,30)])
def degreeRegion35_43 : PrefixRegion := ([(1,15),(7,34)], [(1,10),(3,18),(7,34)])
def degreeRegion35_44 : PrefixRegion := ([(2,10),(3,18)], [(7,34)])
def degreeRegion35_45 : PrefixRegion := ([(7,34)], [(2,10),(3,18)])

def degreeRegions35 : List PrefixRegion := [degreeRegion35_0,degreeRegion35_1,degreeRegion35_2,degreeRegion35_3,degreeRegion35_4,degreeRegion35_5,degreeRegion35_6,degreeRegion35_7,degreeRegion35_8,degreeRegion35_9,degreeRegion35_10,degreeRegion35_11,degreeRegion35_12,degreeRegion35_13,degreeRegion35_14,degreeRegion35_15,degreeRegion35_16,degreeRegion35_17,degreeRegion35_18,degreeRegion35_19,degreeRegion35_20,degreeRegion35_21,degreeRegion35_22,degreeRegion35_23,degreeRegion35_24,degreeRegion35_25,degreeRegion35_26,degreeRegion35_27,degreeRegion35_28,degreeRegion35_29,degreeRegion35_30,degreeRegion35_31,degreeRegion35_32,degreeRegion35_33,degreeRegion35_34,degreeRegion35_35,degreeRegion35_36,degreeRegion35_37,degreeRegion35_38,degreeRegion35_39,degreeRegion35_40,degreeRegion35_41,degreeRegion35_42,degreeRegion35_43,degreeRegion35_44,degreeRegion35_45]

end UniversalTensorSquare
end
end

end OAI
