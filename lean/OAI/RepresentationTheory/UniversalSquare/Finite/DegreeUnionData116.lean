import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData116

namespace OAI

/-! Degree Union Data 116. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions116 : List PrefixRegion := [degreeRegion116_0]

lemma degreeHalfHeight116 : ∀ R ∈ degreeHalfRegions116, firstBound 116 R.1 ≤ 22 := by decide +kernel

lemma degreeHalfWidth116 : ∀ R ∈ degreeHalfRegions116, firstBound 116 R.2 ≤ 22 := by decide +kernel

end UniversalTensorSquare
end

end OAI
