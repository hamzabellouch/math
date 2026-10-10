import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 14. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion14_0 : PrefixRegion := ([(5,11)], [(6,13)])
def degreeRegion14_1 : PrefixRegion := ([(6,13)], [(5,11)])
def degreeRegion14_2 : PrefixRegion := ([(6,13)], [(6,13)])

def degreeRegions14 : List PrefixRegion := [degreeRegion14_0,degreeRegion14_1,degreeRegion14_2]

end UniversalTensorSquare
end
end

end OAI
