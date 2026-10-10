import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion39_0 : PrefixRegion := ([(1,10),(2,12)], [(1,10),(6,34)])
def degreeRegion39_1 : PrefixRegion := ([(1,10),(2,12)], [(1,10),(7,38)])
def degreeRegion39_2 : PrefixRegion := ([(1,10),(2,12),(3,22)], [(1,19),(6,34)])
def degreeRegion39_3 : PrefixRegion := ([(1,10),(2,12),(3,22)], [(1,19),(7,38)])
def degreeRegion39_4 : PrefixRegion := ([(1,10),(3,18)], [(1,19),(5,29)])
def degreeRegion39_5 : PrefixRegion := ([(1,10),(3,18)], [(1,19),(6,34)])
def degreeRegion39_6 : PrefixRegion := ([(1,10),(3,18)], [(1,19),(7,38)])
def degreeRegion39_7 : PrefixRegion := ([(1,10),(3,22),(4,24)], [(1,19),(4,24)])
def degreeRegion39_8 : PrefixRegion := ([(1,10),(3,22),(4,24)], [(1,19),(5,29)])
def degreeRegion39_9 : PrefixRegion := ([(1,10),(3,22),(4,24)], [(1,19),(6,34)])
def degreeRegion39_10 : PrefixRegion := ([(1,10),(3,22),(4,24)], [(1,19),(7,38)])
def degreeRegion39_11 : PrefixRegion := ([(1,10),(3,22),(5,29)], [(1,19),(4,24)])
def degreeRegion39_12 : PrefixRegion := ([(1,10),(3,22),(5,29)], [(1,19),(5,29)])
def degreeRegion39_13 : PrefixRegion := ([(1,10),(3,22),(5,29)], [(1,19),(6,34)])
def degreeRegion39_14 : PrefixRegion := ([(1,10),(3,22),(5,29)], [(1,19),(7,38)])
def degreeRegion39_15 : PrefixRegion := ([(1,10),(3,22),(6,34)], [(1,19),(4,24)])
def degreeRegion39_16 : PrefixRegion := ([(1,10),(3,22),(6,34)], [(1,19),(5,29)])
def degreeRegion39_17 : PrefixRegion := ([(1,10),(3,22),(6,34)], [(1,19),(6,34)])
def degreeRegion39_18 : PrefixRegion := ([(1,10),(3,22),(6,34)], [(1,19),(7,38)])
def degreeRegion39_19 : PrefixRegion := ([(1,10),(3,22),(7,38)], [(1,19),(4,24)])
def degreeRegion39_20 : PrefixRegion := ([(1,10),(3,22),(7,38)], [(1,19),(5,29)])
def degreeRegion39_21 : PrefixRegion := ([(1,10),(3,22),(7,38)], [(1,19),(6,34)])
def degreeRegion39_22 : PrefixRegion := ([(1,10),(3,22),(7,38)], [(1,19),(7,38)])
def degreeRegion39_23 : PrefixRegion := ([(1,10),(4,24)], [(1,10),(4,24)])
def degreeRegion39_24 : PrefixRegion := ([(1,10),(4,24)], [(1,10),(5,29)])
def degreeRegion39_25 : PrefixRegion := ([(1,10),(4,24)], [(1,10),(6,34)])
def degreeRegion39_26 : PrefixRegion := ([(1,10),(4,24)], [(1,10),(7,38)])
def degreeRegion39_27 : PrefixRegion := ([(1,10),(5,29)], [(1,10),(4,24)])
def degreeRegion39_28 : PrefixRegion := ([(1,10),(5,29)], [(1,10),(5,29)])
def degreeRegion39_29 : PrefixRegion := ([(1,10),(5,29)], [(1,10),(6,34)])
def degreeRegion39_30 : PrefixRegion := ([(1,10),(5,29)], [(1,10),(7,38)])
def degreeRegion39_31 : PrefixRegion := ([(1,10),(6,34)], [(1,10),(2,12)])
def degreeRegion39_32 : PrefixRegion := ([(1,10),(6,34)], [(1,10),(4,24)])
def degreeRegion39_33 : PrefixRegion := ([(1,10),(6,34)], [(1,10),(5,29)])
def degreeRegion39_34 : PrefixRegion := ([(1,10),(6,34)], [(1,10),(6,34)])
def degreeRegion39_35 : PrefixRegion := ([(1,10),(6,34)], [(1,10),(7,38)])
def degreeRegion39_36 : PrefixRegion := ([(1,10),(7,38)], [(1,10),(2,12)])
def degreeRegion39_37 : PrefixRegion := ([(1,10),(7,38)], [(1,10),(4,24)])
def degreeRegion39_38 : PrefixRegion := ([(1,10),(7,38)], [(1,10),(5,29)])
def degreeRegion39_39 : PrefixRegion := ([(1,10),(7,38)], [(1,10),(6,34)])
def degreeRegion39_40 : PrefixRegion := ([(1,10),(7,38)], [(1,10),(7,38)])
def degreeRegion39_41 : PrefixRegion := ([(1,19),(3,22),(4,24)], [(1,19),(3,22),(4,24)])
def degreeRegion39_42 : PrefixRegion := ([(1,19),(3,22),(4,24)], [(1,19),(3,22),(5,29)])
def degreeRegion39_43 : PrefixRegion := ([(1,19),(3,22),(4,24)], [(1,19),(3,22),(6,34)])
def degreeRegion39_44 : PrefixRegion := ([(1,19),(3,22),(4,24)], [(1,19),(3,22),(7,38)])
def degreeRegion39_45 : PrefixRegion := ([(1,19),(3,22),(5,29)], [(1,19),(3,22),(4,24)])
def degreeRegion39_46 : PrefixRegion := ([(1,19),(3,22),(5,29)], [(1,19),(3,22),(5,29)])
def degreeRegion39_47 : PrefixRegion := ([(1,19),(3,22),(5,29)], [(1,19),(3,22),(6,34)])
def degreeRegion39_48 : PrefixRegion := ([(1,19),(3,22),(5,29)], [(1,19),(3,22),(7,38)])
def degreeRegion39_49 : PrefixRegion := ([(1,19),(3,22),(5,29)], [(3,18)])
def degreeRegion39_50 : PrefixRegion := ([(1,19),(3,22),(6,34)], [(1,19),(3,22),(4,24)])
def degreeRegion39_51 : PrefixRegion := ([(1,19),(3,22),(6,34)], [(1,19),(3,22),(5,29)])
def degreeRegion39_52 : PrefixRegion := ([(1,19),(3,22),(6,34)], [(1,19),(3,22),(6,34)])
def degreeRegion39_53 : PrefixRegion := ([(1,19),(3,22),(6,34)], [(1,19),(3,22),(7,38)])
def degreeRegion39_54 : PrefixRegion := ([(1,19),(3,22),(6,34)], [(3,18)])
def degreeRegion39_55 : PrefixRegion := ([(1,19),(3,22),(7,38)], [(1,19),(3,22),(4,24)])
def degreeRegion39_56 : PrefixRegion := ([(1,19),(3,22),(7,38)], [(1,19),(3,22),(5,29)])
def degreeRegion39_57 : PrefixRegion := ([(1,19),(3,22),(7,38)], [(1,19),(3,22),(6,34)])
def degreeRegion39_58 : PrefixRegion := ([(1,19),(3,22),(7,38)], [(1,19),(3,22),(7,38)])
def degreeRegion39_59 : PrefixRegion := ([(1,19),(3,22),(7,38)], [(3,18)])
def degreeRegion39_60 : PrefixRegion := ([(1,19),(4,24)], [(1,10),(3,22),(4,24)])
def degreeRegion39_61 : PrefixRegion := ([(1,19),(4,24)], [(1,10),(3,22),(5,29)])
def degreeRegion39_62 : PrefixRegion := ([(1,19),(4,24)], [(1,10),(3,22),(6,34)])
def degreeRegion39_63 : PrefixRegion := ([(1,19),(4,24)], [(1,10),(3,22),(7,38)])
def degreeRegion39_64 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,18)])
def degreeRegion39_65 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,22),(4,24)])
def degreeRegion39_66 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,22),(5,29)])
def degreeRegion39_67 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,22),(6,34)])
def degreeRegion39_68 : PrefixRegion := ([(1,19),(5,29)], [(1,10),(3,22),(7,38)])
def degreeRegion39_69 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(2,12),(3,22)])
def degreeRegion39_70 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,18)])
def degreeRegion39_71 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,22),(4,24)])
def degreeRegion39_72 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,22),(5,29)])
def degreeRegion39_73 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,22),(6,34)])
def degreeRegion39_74 : PrefixRegion := ([(1,19),(6,34)], [(1,10),(3,22),(7,38)])
def degreeRegion39_75 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(2,12),(3,22)])
def degreeRegion39_76 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,18)])
def degreeRegion39_77 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,22),(4,24)])
def degreeRegion39_78 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,22),(5,29)])
def degreeRegion39_79 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,22),(6,34)])
def degreeRegion39_80 : PrefixRegion := ([(1,19),(7,38)], [(1,10),(3,22),(7,38)])
def degreeRegion39_81 : PrefixRegion := ([(2,10),(3,22)], [(7,38)])
def degreeRegion39_82 : PrefixRegion := ([(3,18)], [(1,19),(3,22),(5,29)])
def degreeRegion39_83 : PrefixRegion := ([(3,18)], [(1,19),(3,22),(6,34)])
def degreeRegion39_84 : PrefixRegion := ([(3,18)], [(1,19),(3,22),(7,38)])
def degreeRegion39_85 : PrefixRegion := ([(7,38)], [(2,10),(3,22)])

def degreeRegions39 : List PrefixRegion := [degreeRegion39_0,degreeRegion39_1,degreeRegion39_2,degreeRegion39_3,degreeRegion39_4,degreeRegion39_5,degreeRegion39_6,degreeRegion39_7,degreeRegion39_8,degreeRegion39_9,degreeRegion39_10,degreeRegion39_11,degreeRegion39_12,degreeRegion39_13,degreeRegion39_14,degreeRegion39_15,degreeRegion39_16,degreeRegion39_17,degreeRegion39_18,degreeRegion39_19,degreeRegion39_20,degreeRegion39_21,degreeRegion39_22,degreeRegion39_23,degreeRegion39_24,degreeRegion39_25,degreeRegion39_26,degreeRegion39_27,degreeRegion39_28,degreeRegion39_29,degreeRegion39_30,degreeRegion39_31,degreeRegion39_32,degreeRegion39_33,degreeRegion39_34,degreeRegion39_35,degreeRegion39_36,degreeRegion39_37,degreeRegion39_38,degreeRegion39_39,degreeRegion39_40,degreeRegion39_41,degreeRegion39_42,degreeRegion39_43,degreeRegion39_44,degreeRegion39_45,degreeRegion39_46,degreeRegion39_47,degreeRegion39_48,degreeRegion39_49,degreeRegion39_50,degreeRegion39_51,degreeRegion39_52,degreeRegion39_53,degreeRegion39_54,degreeRegion39_55,degreeRegion39_56,degreeRegion39_57,degreeRegion39_58,degreeRegion39_59,degreeRegion39_60,degreeRegion39_61,degreeRegion39_62,degreeRegion39_63,degreeRegion39_64,degreeRegion39_65,degreeRegion39_66,degreeRegion39_67,degreeRegion39_68,degreeRegion39_69,degreeRegion39_70,degreeRegion39_71,degreeRegion39_72,degreeRegion39_73,degreeRegion39_74,degreeRegion39_75,degreeRegion39_76,degreeRegion39_77,degreeRegion39_78,degreeRegion39_79,degreeRegion39_80,degreeRegion39_81,degreeRegion39_82,degreeRegion39_83,degreeRegion39_84,degreeRegion39_85]

end UniversalTensorSquare
end
end

end OAI
