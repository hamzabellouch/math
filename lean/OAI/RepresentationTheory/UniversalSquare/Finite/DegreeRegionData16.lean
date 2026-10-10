import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 16. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion16_0 : PrefixRegion := ([(3,9)], [(5,15)])
def degreeRegion16_1 : PrefixRegion := ([(4,12)], [(4,12)])
def degreeRegion16_2 : PrefixRegion := ([(4,12)], [(5,15)])
def degreeRegion16_3 : PrefixRegion := ([(5,15)], [(3,9)])
def degreeRegion16_4 : PrefixRegion := ([(5,15)], [(4,12)])
def degreeRegion16_5 : PrefixRegion := ([(5,15)], [(5,15)])

def degreeRegions16 : List PrefixRegion := [degreeRegion16_0,degreeRegion16_1,degreeRegion16_2,degreeRegion16_3,degreeRegion16_4,degreeRegion16_5]

end UniversalTensorSquare
end
end

end OAI
