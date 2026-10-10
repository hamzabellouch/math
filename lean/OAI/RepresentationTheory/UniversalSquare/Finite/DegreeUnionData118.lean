import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeRegionData118

namespace OAI

/-! Degree Union Data 118. -/

section

namespace UniversalTensorSquare

def degreeHalfRegions118 : List PrefixRegion := [degreeRegion118_0]

lemma degreeHalfHeight118 : ∀ R ∈ degreeHalfRegions118, firstBound 118 R.1 ≤ 22 := by decide +kernel

lemma degreeHalfWidth118 : ∀ R ∈ degreeHalfRegions118, firstBound 118 R.2 ≤ 22 := by decide +kernel

end UniversalTensorSquare
end

end OAI
