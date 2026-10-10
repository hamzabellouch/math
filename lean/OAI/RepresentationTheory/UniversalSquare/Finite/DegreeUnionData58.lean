import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData58

namespace OAI

/-! Degree Union Data 58. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions58 : List PrefixRegion := [degreeRegion58_0,degreeRegion58_1,degreeRegion58_2,degreeRegion58_3,degreeRegion58_4,degreeRegion58_5,degreeRegion58_6,degreeRegion58_7,degreeRegion58_9,degreeRegion58_10,degreeRegion58_11,degreeRegion58_12,degreeRegion58_13,degreeRegion58_14,degreeRegion58_15,degreeRegion58_19,degreeRegion58_20,degreeRegion58_21,degreeRegion58_22,degreeRegion58_23,degreeRegion58_24,degreeRegion58_29,degreeRegion58_30,degreeRegion58_31,degreeRegion58_32,degreeRegion58_33,degreeRegion58_38,degreeRegion58_39,degreeRegion58_40,degreeRegion58_41,degreeRegion58_47,degreeRegion58_48,degreeRegion58_54,degreeRegion58_59,degreeRegion58_60]

lemma degreeHalfHeight58 : ∀ R ∈ degreeHalfRegions58, firstBound 58 R.1 ≤ 24 := by decide +kernel

lemma degreeHalfWidth58 : ∀ R ∈ degreeHalfRegions58, firstBound 58 R.2 ≤ 14 := by decide +kernel

end UniversalTensorSquare
end

end OAI
