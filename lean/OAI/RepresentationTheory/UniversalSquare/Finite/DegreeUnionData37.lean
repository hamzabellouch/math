import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData37

namespace OAI

/-! Degree Union Data 37. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions37 : List PrefixRegion := [degreeRegion37_0,degreeRegion37_1,degreeRegion37_2,degreeRegion37_3,degreeRegion37_4,degreeRegion37_5,degreeRegion37_6,degreeRegion37_7,degreeRegion37_8,degreeRegion37_9,degreeRegion37_10,degreeRegion37_11,degreeRegion37_12,degreeRegion37_13,degreeRegion37_14,degreeRegion37_15,degreeRegion37_16,degreeRegion37_17,degreeRegion37_18,degreeRegion37_19,degreeRegion37_20,degreeRegion37_21,degreeRegion37_22,degreeRegion37_23,degreeRegion37_24,degreeRegion37_25,degreeRegion37_26,degreeRegion37_27,degreeRegion37_28,degreeRegion37_29,degreeRegion37_30,degreeRegion37_31,degreeRegion37_32,degreeRegion37_33,degreeRegion37_34,degreeRegion37_35,degreeRegion37_36,degreeRegion37_37,degreeRegion37_38,degreeRegion37_39,degreeRegion37_40,degreeRegion37_41,degreeRegion37_42,degreeRegion37_44,degreeRegion37_45,degreeRegion37_46,degreeRegion37_47,degreeRegion37_50,degreeRegion37_51,degreeRegion37_52,degreeRegion37_56,degreeRegion37_57,degreeRegion37_62,degreeRegion37_63,degreeRegion37_64,degreeRegion37_65,degreeRegion37_66,degreeRegion37_67,degreeRegion37_69,degreeRegion37_70,degreeRegion37_71,degreeRegion37_72,degreeRegion37_75,degreeRegion37_76,degreeRegion37_77]

lemma degreeHalfHeight37 : ∀ R ∈ degreeHalfRegions37, firstBound 37 R.1 ≤ 17 := by decide +kernel

lemma degreeHalfWidth37 : ∀ R ∈ degreeHalfRegions37, firstBound 37 R.2 ≤ 17 := by decide +kernel

end UniversalTensorSquare
end

end OAI
