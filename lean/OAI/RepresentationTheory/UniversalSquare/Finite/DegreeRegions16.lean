import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves16

namespace OAI

/-! Degree Regions 16. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck16 : ∀ h ≤ 15,
    checkRegionPrefixes (quickResidual 4 3 degreeQs16 degreeTree16) h 16 15 degreeHalfRegions16 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch16_0
  · exact degreeUnionBranch16_1
  · exact degreeUnionBranch16_2
  · exact degreeUnionBranch16_3
  · exact degreeUnionBranch16_4
  · exact degreeUnionBranch16_5
  · exact degreeUnionBranch16_6
  · exact degreeUnionBranch16_7
  · exact degreeUnionBranch16_8
  · exact degreeUnionBranch16_9
  · exact degreeUnionBranch16_10
  · exact degreeUnionBranch16_11
  · exact degreeUnionBranch16_12
  · exact degreeUnionBranch16_13
  · exact degreeUnionBranch16_14
  · exact degreeUnionBranch16_15

lemma degreeHalfCover16 : ∀ R ∈ degreeRegions16,
    R ∈ degreeHalfRegions16 ∨ (R.2,R.1) ∈ degreeHalfRegions16 := by decide +kernel

lemma degreeDiagramRegionsChecked16 : ∀ R ∈ degreeRegions16,
    ∀ μ : YoungDiagram, μ.card = 16 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP16 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck16 degreeHalfHeight16 degreeHalfWidth16
    degreeHalfCover16

end UniversalTensorSquare
end

end OAI
