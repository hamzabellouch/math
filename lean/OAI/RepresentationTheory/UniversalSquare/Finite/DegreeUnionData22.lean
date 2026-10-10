import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData22

namespace OAI

/-! Degree Union Data 22. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions22 : List PrefixRegion := [degreeRegion22_0,degreeRegion22_1,degreeRegion22_2,degreeRegion22_3,degreeRegion22_4,degreeRegion22_5,degreeRegion22_8,degreeRegion22_9,degreeRegion22_14]

lemma degreeHalfHeight22 : ∀ R ∈ degreeHalfRegions22, firstBound 22 R.1 ≤ 21 := by decide +kernel

lemma degreeHalfWidth22 : ∀ R ∈ degreeHalfRegions22, firstBound 22 R.2 ≤ 21 := by decide +kernel

end UniversalTensorSquare
end

end OAI
