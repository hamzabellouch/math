import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData26

namespace OAI

/-! Degree Union Data 26. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions26 : List PrefixRegion := [degreeRegion26_0,degreeRegion26_1,degreeRegion26_2,degreeRegion26_3,degreeRegion26_4,degreeRegion26_6,degreeRegion26_7,degreeRegion26_8,degreeRegion26_12,degreeRegion26_13,degreeRegion26_18]

lemma degreeHalfHeight26 : ∀ R ∈ degreeHalfRegions26, firstBound 26 R.1 ≤ 25 := by decide +kernel

lemma degreeHalfWidth26 : ∀ R ∈ degreeHalfRegions26, firstBound 26 R.2 ≤ 25 := by decide +kernel

end UniversalTensorSquare
end

end OAI
