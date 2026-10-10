import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves64

namespace OAI

/-! Degree Regions 64. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck64 : ∀ h ≤ 30,
    checkRegionPrefixes (quickResidual 8 14 degreeQs64 degreeTree64) h 64 30 degreeHalfRegions64 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch64_0
  · exact degreeUnionBranch64_1
  · exact degreeUnionBranch64_2
  · exact degreeUnionBranch64_3
  · exact degreeUnionBranch64_4
  · exact degreeUnionBranch64_5
  · exact degreeUnionBranch64_6
  · exact degreeUnionBranch64_7
  · exact degreeUnionBranch64_8
  · exact degreeUnionBranch64_9
  · exact degreeUnionBranch64_10
  · exact degreeUnionBranch64_11
  · exact degreeUnionBranch64_12
  · exact degreeUnionBranch64_13
  · exact degreeUnionBranch64_14
  · exact degreeUnionBranch64_15
  · exact degreeUnionBranch64_16
  · exact degreeUnionBranch64_17
  · exact degreeUnionBranch64_18
  · exact degreeUnionBranch64_19
  · exact degreeUnionBranch64_20
  · exact degreeUnionBranch64_21
  · exact degreeUnionBranch64_22
  · exact degreeUnionBranch64_23
  · exact degreeUnionBranch64_24
  · exact degreeUnionBranch64_25
  · exact degreeUnionBranch64_26
  · exact degreeUnionBranch64_27
  · exact degreeUnionBranch64_28
  · exact degreeUnionBranch64_29
  · exact degreeUnionBranch64_30

lemma degreeHalfCover64 : ∀ R ∈ degreeRegions64,
    R ∈ degreeHalfRegions64 ∨ (R.2,R.1) ∈ degreeHalfRegions64 := by decide +kernel

lemma degreeDiagramRegionsChecked64 : ∀ R ∈ degreeRegions64,
    ∀ μ : YoungDiagram, μ.card = 64 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP64 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck64 degreeHalfHeight64 degreeHalfWidth64
    degreeHalfCover64

end UniversalTensorSquare
end

end OAI
