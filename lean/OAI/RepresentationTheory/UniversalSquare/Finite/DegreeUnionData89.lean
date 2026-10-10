import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData89

namespace OAI

/-! Degree Union Data 89. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions89 : List PrefixRegion := [degreeRegion89_0,degreeRegion89_1,degreeRegion89_2,degreeRegion89_3]

lemma degreeHalfHeight89 : ∀ R ∈ degreeHalfRegions89, firstBound 89 R.1 ≤ 18 := by decide +kernel

lemma degreeHalfWidth89 : ∀ R ∈ degreeHalfRegions89, firstBound 89 R.2 ≤ 18 := by decide +kernel

end UniversalTensorSquare
end

end OAI
