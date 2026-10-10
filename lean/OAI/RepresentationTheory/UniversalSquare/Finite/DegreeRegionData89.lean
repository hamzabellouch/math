import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 89. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion89_0 : PrefixRegion := ([(1,10),(2,42),(3,44)], [(2,18),(3,44),(5,47)])
def degreeRegion89_1 : PrefixRegion := ([(1,18),(2,20),(3,44)], [(2,18),(3,44),(5,47)])
def degreeRegion89_2 : PrefixRegion := ([(1,18),(3,30)], [(2,18),(3,44),(5,47)])
def degreeRegion89_3 : PrefixRegion := ([(1,18),(4,40)], [(2,18),(3,44),(5,47)])
def degreeRegion89_4 : PrefixRegion := ([(2,18),(3,44),(5,47)], [(1,10),(2,42),(3,44)])
def degreeRegion89_5 : PrefixRegion := ([(2,18),(3,44),(5,47)], [(1,18),(2,20),(3,44)])
def degreeRegion89_6 : PrefixRegion := ([(2,18),(3,44),(5,47)], [(1,18),(3,30)])
def degreeRegion89_7 : PrefixRegion := ([(2,18),(3,44),(5,47)], [(1,18),(4,40)])

def degreeRegions89 : List PrefixRegion := [degreeRegion89_0,degreeRegion89_1,degreeRegion89_2,degreeRegion89_3,degreeRegion89_4,degreeRegion89_5,degreeRegion89_6,degreeRegion89_7]

end UniversalTensorSquare
end
end

end OAI
