import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData18

namespace OAI

/-! Degree Union Data 18. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions18 : List PrefixRegion := [degreeRegion18_0,degreeRegion18_1,degreeRegion18_2,degreeRegion18_4,degreeRegion18_5,degreeRegion18_9]

lemma degreeHalfHeight18 : ∀ R ∈ degreeHalfRegions18, firstBound 18 R.1 ≤ 17 := by decide +kernel

lemma degreeHalfWidth18 : ∀ R ∈ degreeHalfRegions18, firstBound 18 R.2 ≤ 17 := by decide +kernel

end UniversalTensorSquare
end

end OAI
