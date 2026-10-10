import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves41

namespace OAI

/-! Degree Regions 41. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck41 : ∀ h ≤ 21,
    checkRegionPrefixes (quickResidual 6 10 degreeQs41 degreeTree41) h 41 21 degreeHalfRegions41 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch41_0
  · exact degreeUnionBranch41_1
  · exact degreeUnionBranch41_2
  · exact degreeUnionBranch41_3
  · exact degreeUnionBranch41_4
  · exact degreeUnionBranch41_5
  · exact degreeUnionBranch41_6
  · exact degreeUnionBranch41_7
  · exact degreeUnionBranch41_8
  · exact degreeUnionBranch41_9
  · exact degreeUnionBranch41_10
  · exact degreeUnionBranch41_11
  · exact degreeUnionBranch41_12
  · exact degreeUnionBranch41_13
  · exact degreeUnionBranch41_14
  · exact degreeUnionBranch41_15
  · exact degreeUnionBranch41_16
  · exact degreeUnionBranch41_17
  · exact degreeUnionBranch41_18
  · exact degreeUnionBranch41_19
  · exact degreeUnionBranch41_20
  · exact degreeUnionBranch41_21

lemma degreeHalfCover41 : ∀ R ∈ degreeRegions41,
    R ∈ degreeHalfRegions41 ∨ (R.2,R.1) ∈ degreeHalfRegions41 := by decide +kernel

lemma degreeDiagramRegionsChecked41 : ∀ R ∈ degreeRegions41,
    ∀ μ : YoungDiagram, μ.card = 41 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP41 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck41 degreeHalfHeight41 degreeHalfWidth41
    degreeHalfCover41

end UniversalTensorSquare
end

end OAI
