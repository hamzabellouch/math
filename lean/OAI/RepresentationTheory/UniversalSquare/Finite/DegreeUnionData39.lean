import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData39

namespace OAI

/-! Degree Union Data 39. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions39 : List PrefixRegion := [degreeRegion39_0,degreeRegion39_1,degreeRegion39_2,degreeRegion39_3,degreeRegion39_4,degreeRegion39_5,degreeRegion39_6,degreeRegion39_7,degreeRegion39_8,degreeRegion39_9,degreeRegion39_10,degreeRegion39_11,degreeRegion39_12,degreeRegion39_13,degreeRegion39_14,degreeRegion39_15,degreeRegion39_16,degreeRegion39_17,degreeRegion39_18,degreeRegion39_19,degreeRegion39_20,degreeRegion39_21,degreeRegion39_22,degreeRegion39_23,degreeRegion39_24,degreeRegion39_25,degreeRegion39_26,degreeRegion39_28,degreeRegion39_29,degreeRegion39_30,degreeRegion39_34,degreeRegion39_35,degreeRegion39_40,degreeRegion39_41,degreeRegion39_42,degreeRegion39_43,degreeRegion39_44,degreeRegion39_46,degreeRegion39_47,degreeRegion39_48,degreeRegion39_49,degreeRegion39_52,degreeRegion39_53,degreeRegion39_54,degreeRegion39_58,degreeRegion39_59,degreeRegion39_81]

lemma degreeHalfHeight39 : ∀ R ∈ degreeHalfRegions39, firstBound 39 R.1 ≤ 19 := by decide +kernel

lemma degreeHalfWidth39 : ∀ R ∈ degreeHalfRegions39, firstBound 39 R.2 ≤ 38 := by decide +kernel

end UniversalTensorSquare
end

end OAI
