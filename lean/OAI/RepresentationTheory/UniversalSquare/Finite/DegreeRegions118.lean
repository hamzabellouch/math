import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves118

namespace OAI

/-! Degree Regions 118. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck118 : ∀ h ≤ 22,
    checkRegionPrefixes (quickResidual 12 20 degreeQs118 degreeTree118) h 118 22 degreeHalfRegions118 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch118_0
  · exact degreeUnionBranch118_1
  · exact degreeUnionBranch118_2
  · exact degreeUnionBranch118_3
  · exact degreeUnionBranch118_4
  · exact degreeUnionBranch118_5
  · exact degreeUnionBranch118_6
  · exact degreeUnionBranch118_7
  · exact degreeUnionBranch118_8
  · exact degreeUnionBranch118_9
  · exact degreeUnionBranch118_10
  · exact degreeUnionBranch118_11
  · exact degreeUnionBranch118_12
  · exact degreeUnionBranch118_13
  · exact degreeUnionBranch118_14
  · exact degreeUnionBranch118_15
  · exact degreeUnionBranch118_16
  · exact degreeUnionBranch118_17
  · exact degreeUnionBranch118_18
  · exact degreeUnionBranch118_19
  · exact degreeUnionBranch118_20
  · exact degreeUnionBranch118_21
  · exact degreeUnionBranch118_22

lemma degreeHalfCover118 : ∀ R ∈ degreeRegions118,
    R ∈ degreeHalfRegions118 ∨ (R.2,R.1) ∈ degreeHalfRegions118 := by decide +kernel

lemma degreeDiagramRegionsChecked118 : ∀ R ∈ degreeRegions118,
    ∀ μ : YoungDiagram, μ.card = 118 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP118 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck118 degreeHalfHeight118 degreeHalfWidth118
    degreeHalfCover118

end UniversalTensorSquare
end

end OAI
