import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion20_0 : PrefixRegion := ([(1,5)], [(1,5)])
def degreeRegion20_1 : PrefixRegion := ([(1,5)], [(2,9)])
def degreeRegion20_2 : PrefixRegion := ([(1,5)], [(3,13)])
def degreeRegion20_3 : PrefixRegion := ([(1,5)], [(4,16)])
def degreeRegion20_4 : PrefixRegion := ([(2,9)], [(1,5)])
def degreeRegion20_5 : PrefixRegion := ([(2,9)], [(4,16)])
def degreeRegion20_6 : PrefixRegion := ([(2,9)], [(5,19)])
def degreeRegion20_7 : PrefixRegion := ([(3,13)], [(1,5)])
def degreeRegion20_8 : PrefixRegion := ([(3,13)], [(3,13)])
def degreeRegion20_9 : PrefixRegion := ([(3,13)], [(4,16)])
def degreeRegion20_10 : PrefixRegion := ([(3,13)], [(5,19)])
def degreeRegion20_11 : PrefixRegion := ([(4,16)], [(1,5)])
def degreeRegion20_12 : PrefixRegion := ([(4,16)], [(2,9)])
def degreeRegion20_13 : PrefixRegion := ([(4,16)], [(3,13)])
def degreeRegion20_14 : PrefixRegion := ([(4,16)], [(4,16)])
def degreeRegion20_15 : PrefixRegion := ([(4,16)], [(5,19)])
def degreeRegion20_16 : PrefixRegion := ([(5,19)], [(2,9)])
def degreeRegion20_17 : PrefixRegion := ([(5,19)], [(3,13)])
def degreeRegion20_18 : PrefixRegion := ([(5,19)], [(4,16)])
def degreeRegion20_19 : PrefixRegion := ([(5,19)], [(5,19)])

def degreeRegions20 : List PrefixRegion := [degreeRegion20_0,degreeRegion20_1,degreeRegion20_2,degreeRegion20_3,degreeRegion20_4,degreeRegion20_5,degreeRegion20_6,degreeRegion20_7,degreeRegion20_8,degreeRegion20_9,degreeRegion20_10,degreeRegion20_11,degreeRegion20_12,degreeRegion20_13,degreeRegion20_14,degreeRegion20_15,degreeRegion20_16,degreeRegion20_17,degreeRegion20_18,degreeRegion20_19]

end UniversalTensorSquare
end
end

end OAI
