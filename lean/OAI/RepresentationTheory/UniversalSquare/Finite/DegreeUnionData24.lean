import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData24

namespace OAI

/-! Degree Union Data 24. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions24 : List PrefixRegion := [degreeRegion24_0,degreeRegion24_1,degreeRegion24_2,degreeRegion24_3,degreeRegion24_4,degreeRegion24_6,degreeRegion24_7,degreeRegion24_8,degreeRegion24_9,degreeRegion24_12,degreeRegion24_13,degreeRegion24_14,degreeRegion24_18,degreeRegion24_19,degreeRegion24_24]

lemma degreeHalfHeight24 : ∀ R ∈ degreeHalfRegions24, firstBound 24 R.1 ≤ 23 := by decide +kernel

lemma degreeHalfWidth24 : ∀ R ∈ degreeHalfRegions24, firstBound 24 R.2 ≤ 23 := by decide +kernel

end UniversalTensorSquare
end

end OAI
