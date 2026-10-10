import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData31

namespace OAI

/-! Degree Union Data 31. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions31 : List PrefixRegion := [degreeRegion31_0,degreeRegion31_1,degreeRegion31_2,degreeRegion31_3,degreeRegion31_4,degreeRegion31_6,degreeRegion31_7,degreeRegion31_8,degreeRegion31_11,degreeRegion31_12,degreeRegion31_16,degreeRegion31_19]

lemma degreeHalfHeight31 : ∀ R ∈ degreeHalfRegions31, firstBound 31 R.1 ≤ 10 := by decide +kernel

lemma degreeHalfWidth31 : ∀ R ∈ degreeHalfRegions31, firstBound 31 R.2 ≤ 30 := by decide +kernel

end UniversalTensorSquare
end

end OAI
