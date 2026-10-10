import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.ResidualTrees

namespace OAI

/-! Degree Region Data 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

def degreeRegion19_0 : PrefixRegion := ([(1,8),(5,14)], [(1,8),(5,14)])
def degreeRegion19_1 : PrefixRegion := ([(1,8),(7,18)], [(1,8),(7,18)])

def degreeRegions19 : List PrefixRegion := [degreeRegion19_0,degreeRegion19_1]

end UniversalTensorSquare
end
end

end OAI
