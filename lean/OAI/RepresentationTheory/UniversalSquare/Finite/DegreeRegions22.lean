import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves22

namespace OAI

/-! Degree Regions 22. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck22 : ∀ h ≤ 21,
    checkRegionPrefixes (quickResidual 4 6 degreeQs22 degreeTree22) h 22 21 degreeHalfRegions22 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch22_0
  · exact degreeUnionBranch22_1
  · exact degreeUnionBranch22_2
  · exact degreeUnionBranch22_3
  · exact degreeUnionBranch22_4
  · exact degreeUnionBranch22_5
  · exact degreeUnionBranch22_6
  · exact degreeUnionBranch22_7
  · exact degreeUnionBranch22_8
  · exact degreeUnionBranch22_9
  · exact degreeUnionBranch22_10
  · exact degreeUnionBranch22_11
  · exact degreeUnionBranch22_12
  · exact degreeUnionBranch22_13
  · exact degreeUnionBranch22_14
  · exact degreeUnionBranch22_15
  · exact degreeUnionBranch22_16
  · exact degreeUnionBranch22_17
  · exact degreeUnionBranch22_18
  · exact degreeUnionBranch22_19
  · exact degreeUnionBranch22_20
  · exact degreeUnionBranch22_21

lemma degreeHalfCover22 : ∀ R ∈ degreeRegions22,
    R ∈ degreeHalfRegions22 ∨ (R.2,R.1) ∈ degreeHalfRegions22 := by decide +kernel

lemma degreeDiagramRegionsChecked22 : ∀ R ∈ degreeRegions22,
    ∀ μ : YoungDiagram, μ.card = 22 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP22 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck22 degreeHalfHeight22 degreeHalfWidth22
    degreeHalfCover22

end UniversalTensorSquare
end

end OAI
