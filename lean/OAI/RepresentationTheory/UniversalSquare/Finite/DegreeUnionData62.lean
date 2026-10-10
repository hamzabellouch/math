import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData62

namespace OAI

/-! Degree Union Data 62. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions62 : List PrefixRegion := [degreeRegion62_0,degreeRegion62_1,degreeRegion62_2,degreeRegion62_3,degreeRegion62_5,degreeRegion62_6,degreeRegion62_7,degreeRegion62_8,degreeRegion62_11,degreeRegion62_12,degreeRegion62_13,degreeRegion62_14,degreeRegion62_15,degreeRegion62_16,degreeRegion62_17,degreeRegion62_18,degreeRegion62_19,degreeRegion62_20,degreeRegion62_21,degreeRegion62_22,degreeRegion62_23,degreeRegion62_24,degreeRegion62_25,degreeRegion62_26,degreeRegion62_29,degreeRegion62_30,degreeRegion62_31,degreeRegion62_32,degreeRegion62_33,degreeRegion62_34,degreeRegion62_35,degreeRegion62_36,degreeRegion62_37,degreeRegion62_38,degreeRegion62_39,degreeRegion62_40,degreeRegion62_41,degreeRegion62_42,degreeRegion62_46,degreeRegion62_47,degreeRegion62_48,degreeRegion62_49,degreeRegion62_50,degreeRegion62_51,degreeRegion62_56,degreeRegion62_57,degreeRegion62_58,degreeRegion62_59,degreeRegion62_60,degreeRegion62_67,degreeRegion62_68,degreeRegion62_69,degreeRegion62_70,degreeRegion62_77,degreeRegion62_78,degreeRegion62_79,degreeRegion62_87,degreeRegion62_88,degreeRegion62_99,degreeRegion62_102,degreeRegion62_108,degreeRegion62_109]

lemma degreeHalfHeight62 : ∀ R ∈ degreeHalfRegions62, firstBound 62 R.1 ≤ 28 := by decide +kernel

lemma degreeHalfWidth62 : ∀ R ∈ degreeHalfRegions62, firstBound 62 R.2 ≤ 28 := by decide +kernel

end UniversalTensorSquare
end

end OAI
