import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion22_0 : PrefixRegion := ([(2,8)], [(6,21)])
def degreeRegion22_1 : PrefixRegion := ([(3,12)], [(5,18)])
def degreeRegion22_2 : PrefixRegion := ([(3,12)], [(6,21)])
def degreeRegion22_3 : PrefixRegion := ([(4,15)], [(4,15)])
def degreeRegion22_4 : PrefixRegion := ([(4,15)], [(5,18)])
def degreeRegion22_5 : PrefixRegion := ([(4,15)], [(6,21)])
def degreeRegion22_6 : PrefixRegion := ([(5,18)], [(3,12)])
def degreeRegion22_7 : PrefixRegion := ([(5,18)], [(4,15)])
def degreeRegion22_8 : PrefixRegion := ([(5,18)], [(5,18)])
def degreeRegion22_9 : PrefixRegion := ([(5,18)], [(6,21)])
def degreeRegion22_10 : PrefixRegion := ([(6,21)], [(2,8)])
def degreeRegion22_11 : PrefixRegion := ([(6,21)], [(3,12)])
def degreeRegion22_12 : PrefixRegion := ([(6,21)], [(4,15)])
def degreeRegion22_13 : PrefixRegion := ([(6,21)], [(5,18)])
def degreeRegion22_14 : PrefixRegion := ([(6,21)], [(6,21)])

def degreeRegions22 : List PrefixRegion := [degreeRegion22_0,degreeRegion22_1,degreeRegion22_2,degreeRegion22_3,degreeRegion22_4,degreeRegion22_5,degreeRegion22_6,degreeRegion22_7,degreeRegion22_8,degreeRegion22_9,degreeRegion22_10,degreeRegion22_11,degreeRegion22_12,degreeRegion22_13,degreeRegion22_14]

end UniversalTensorSquare
end
end

end OAI
