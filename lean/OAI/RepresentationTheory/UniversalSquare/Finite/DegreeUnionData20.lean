import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData20

namespace OAI

/-! Degree Union Data 20. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions20 : List PrefixRegion := [degreeRegion20_0,degreeRegion20_1,degreeRegion20_2,degreeRegion20_3,degreeRegion20_5,degreeRegion20_6,degreeRegion20_8,degreeRegion20_9,degreeRegion20_10,degreeRegion20_14,degreeRegion20_15,degreeRegion20_19]

lemma degreeHalfHeight20 : ∀ R ∈ degreeHalfRegions20, firstBound 20 R.1 ≤ 19 := by decide +kernel

lemma degreeHalfWidth20 : ∀ R ∈ degreeHalfRegions20, firstBound 20 R.2 ≤ 19 := by decide +kernel

end UniversalTensorSquare
end

end OAI
