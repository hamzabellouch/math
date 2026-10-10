import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData43

namespace OAI

/-! Degree Union Data 43. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions43 : List PrefixRegion := [degreeRegion43_0,degreeRegion43_1,degreeRegion43_2,degreeRegion43_3,degreeRegion43_4,degreeRegion43_5,degreeRegion43_6,degreeRegion43_7,degreeRegion43_8,degreeRegion43_9,degreeRegion43_10,degreeRegion43_12,degreeRegion43_13,degreeRegion43_14,degreeRegion43_15,degreeRegion43_16,degreeRegion43_17,degreeRegion43_18,degreeRegion43_19,degreeRegion43_21,degreeRegion43_22,degreeRegion43_23,degreeRegion43_24,degreeRegion43_25,degreeRegion43_26,degreeRegion43_27,degreeRegion43_28,degreeRegion43_29,degreeRegion43_30,degreeRegion43_31,degreeRegion43_32,degreeRegion43_33,degreeRegion43_34,degreeRegion43_35,degreeRegion43_36,degreeRegion43_38,degreeRegion43_39,degreeRegion43_40,degreeRegion43_41,degreeRegion43_44,degreeRegion43_45,degreeRegion43_46,degreeRegion43_50,degreeRegion43_51,degreeRegion43_55,degreeRegion43_56,degreeRegion43_57,degreeRegion43_58,degreeRegion43_59,degreeRegion43_60,degreeRegion43_61,degreeRegion43_63,degreeRegion43_64,degreeRegion43_65,degreeRegion43_66,degreeRegion43_67,degreeRegion43_70,degreeRegion43_71,degreeRegion43_72,degreeRegion43_73,degreeRegion43_78,degreeRegion43_79,degreeRegion43_100,degreeRegion43_112,degreeRegion43_113]

lemma degreeHalfHeight43 : ∀ R ∈ degreeHalfRegions43, firstBound 43 R.1 ≤ 23 := by decide +kernel

lemma degreeHalfWidth43 : ∀ R ∈ degreeHalfRegions43, firstBound 43 R.2 ≤ 42 := by decide +kernel

end UniversalTensorSquare
end

end OAI
