import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData14

namespace OAI

/-! Degree Union Data 14. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions14 : List PrefixRegion := [degreeRegion14_0,degreeRegion14_2]

lemma degreeHalfHeight14 : ∀ R ∈ degreeHalfRegions14, firstBound 14 R.1 ≤ 13 := by decide +kernel

lemma degreeHalfWidth14 : ∀ R ∈ degreeHalfRegions14, firstBound 14 R.2 ≤ 13 := by decide +kernel

end UniversalTensorSquare
end

end OAI
