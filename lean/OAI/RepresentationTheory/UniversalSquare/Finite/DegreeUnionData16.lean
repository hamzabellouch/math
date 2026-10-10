import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData16

namespace OAI

/-! Degree Union Data 16. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions16 : List PrefixRegion := [degreeRegion16_0,degreeRegion16_1,degreeRegion16_2,degreeRegion16_5]

lemma degreeHalfHeight16 : ∀ R ∈ degreeHalfRegions16, firstBound 16 R.1 ≤ 15 := by decide +kernel

lemma degreeHalfWidth16 : ∀ R ∈ degreeHalfRegions16, firstBound 16 R.2 ≤ 15 := by decide +kernel

end UniversalTensorSquare
end

end OAI
