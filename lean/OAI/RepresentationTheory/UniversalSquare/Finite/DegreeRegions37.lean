import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves37

namespace OAI

/-! Degree Regions 37. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck37 : ∀ h ≤ 17,
    checkRegionPrefixes (quickResidual 6 8 degreeQs37 degreeTree37) h 37 17 degreeHalfRegions37 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch37_0
  · exact degreeUnionBranch37_1
  · exact degreeUnionBranch37_2
  · exact degreeUnionBranch37_3
  · exact degreeUnionBranch37_4
  · exact degreeUnionBranch37_5
  · exact degreeUnionBranch37_6
  · exact degreeUnionBranch37_7
  · exact degreeUnionBranch37_8
  · exact degreeUnionBranch37_9
  · exact degreeUnionBranch37_10
  · exact degreeUnionBranch37_11
  · exact degreeUnionBranch37_12
  · exact degreeUnionBranch37_13
  · exact degreeUnionBranch37_14
  · exact degreeUnionBranch37_15
  · exact degreeUnionBranch37_16
  · exact degreeUnionBranch37_17

lemma degreeHalfCover37 : ∀ R ∈ degreeRegions37,
    R ∈ degreeHalfRegions37 ∨ (R.2,R.1) ∈ degreeHalfRegions37 := by decide +kernel

lemma degreeDiagramRegionsChecked37 : ∀ R ∈ degreeRegions37,
    ∀ μ : YoungDiagram, μ.card = 37 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP37 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck37 degreeHalfHeight37 degreeHalfWidth37
    degreeHalfCover37

end UniversalTensorSquare
end

end OAI
