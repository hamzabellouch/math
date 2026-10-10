import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves116

namespace OAI

/-! Degree Regions 116. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck116 : ∀ h ≤ 22,
    checkRegionPrefixes (quickResidual 12 19 degreeQs116 degreeTree116) h 116 22 degreeHalfRegions116 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch116_0
  · exact degreeUnionBranch116_1
  · exact degreeUnionBranch116_2
  · exact degreeUnionBranch116_3
  · exact degreeUnionBranch116_4
  · exact degreeUnionBranch116_5
  · exact degreeUnionBranch116_6
  · exact degreeUnionBranch116_7
  · exact degreeUnionBranch116_8
  · exact degreeUnionBranch116_9
  · exact degreeUnionBranch116_10
  · exact degreeUnionBranch116_11
  · exact degreeUnionBranch116_12
  · exact degreeUnionBranch116_13
  · exact degreeUnionBranch116_14
  · exact degreeUnionBranch116_15
  · exact degreeUnionBranch116_16
  · exact degreeUnionBranch116_17
  · exact degreeUnionBranch116_18
  · exact degreeUnionBranch116_19
  · exact degreeUnionBranch116_20
  · exact degreeUnionBranch116_21
  · exact degreeUnionBranch116_22

lemma degreeHalfCover116 : ∀ R ∈ degreeRegions116,
    R ∈ degreeHalfRegions116 ∨ (R.2,R.1) ∈ degreeHalfRegions116 := by decide +kernel

lemma degreeDiagramRegionsChecked116 : ∀ R ∈ degreeRegions116,
    ∀ μ : YoungDiagram, μ.card = 116 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP116 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck116 degreeHalfHeight116 degreeHalfWidth116
    degreeHalfCover116

end UniversalTensorSquare
end

end OAI
