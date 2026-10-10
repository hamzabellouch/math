import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion18_0 : PrefixRegion := ([(3,9)], [(6,17)])
def degreeRegion18_1 : PrefixRegion := ([(4,12)], [(5,15)])
def degreeRegion18_2 : PrefixRegion := ([(4,12)], [(6,17)])
def degreeRegion18_3 : PrefixRegion := ([(5,15)], [(4,12)])
def degreeRegion18_4 : PrefixRegion := ([(5,15)], [(5,15)])
def degreeRegion18_5 : PrefixRegion := ([(5,15)], [(6,17)])
def degreeRegion18_6 : PrefixRegion := ([(6,17)], [(3,9)])
def degreeRegion18_7 : PrefixRegion := ([(6,17)], [(4,12)])
def degreeRegion18_8 : PrefixRegion := ([(6,17)], [(5,15)])
def degreeRegion18_9 : PrefixRegion := ([(6,17)], [(6,17)])

def degreeRegions18 : List PrefixRegion := [degreeRegion18_0,degreeRegion18_1,degreeRegion18_2,degreeRegion18_3,degreeRegion18_4,degreeRegion18_5,degreeRegion18_6,degreeRegion18_7,degreeRegion18_8,degreeRegion18_9]

end UniversalTensorSquare
end
end

end OAI
