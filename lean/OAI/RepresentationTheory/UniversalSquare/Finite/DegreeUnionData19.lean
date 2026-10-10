import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData19

namespace OAI

/-! Degree Union Data 19. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions19 : List PrefixRegion := [degreeRegion19_0,degreeRegion19_1]

lemma degreeHalfHeight19 : ∀ R ∈ degreeHalfRegions19, firstBound 19 R.1 ≤ 8 := by decide +kernel

lemma degreeHalfWidth19 : ∀ R ∈ degreeHalfRegions19, firstBound 19 R.2 ≤ 8 := by decide +kernel

end UniversalTensorSquare
end

end OAI
