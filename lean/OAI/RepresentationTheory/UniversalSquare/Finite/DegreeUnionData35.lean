import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData35

namespace OAI

/-! Degree Union Data 35. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions35 : List PrefixRegion := [degreeRegion35_0,degreeRegion35_1,degreeRegion35_2,degreeRegion35_3,degreeRegion35_4,degreeRegion35_5,degreeRegion35_6,degreeRegion35_7,degreeRegion35_8,degreeRegion35_9,degreeRegion35_10,degreeRegion35_11,degreeRegion35_12,degreeRegion35_13,degreeRegion35_14,degreeRegion35_15,degreeRegion35_16,degreeRegion35_18,degreeRegion35_19,degreeRegion35_20,degreeRegion35_23,degreeRegion35_24,degreeRegion35_28,degreeRegion35_29,degreeRegion35_44]

lemma degreeHalfHeight35 : ∀ R ∈ degreeHalfRegions35, firstBound 35 R.1 ≤ 15 := by decide +kernel

lemma degreeHalfWidth35 : ∀ R ∈ degreeHalfRegions35, firstBound 35 R.2 ≤ 34 := by decide +kernel

end UniversalTensorSquare
end

end OAI
