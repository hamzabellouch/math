import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves18

namespace OAI

/-! Degree Regions 18. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck18 : ∀ h ≤ 17,
    checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) h 18 17 degreeHalfRegions18 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch18_0
  · exact degreeUnionBranch18_1
  · exact degreeUnionBranch18_2
  · exact degreeUnionBranch18_3
  · exact degreeUnionBranch18_4
  · exact degreeUnionBranch18_5
  · exact degreeUnionBranch18_6
  · exact degreeUnionBranch18_7
  · exact degreeUnionBranch18_8
  · exact degreeUnionBranch18_9
  · exact degreeUnionBranch18_10
  · exact degreeUnionBranch18_11
  · exact degreeUnionBranch18_12
  · exact degreeUnionBranch18_13
  · exact degreeUnionBranch18_14
  · exact degreeUnionBranch18_15
  · exact degreeUnionBranch18_16
  · exact degreeUnionBranch18_17

lemma degreeHalfCover18 : ∀ R ∈ degreeRegions18,
    R ∈ degreeHalfRegions18 ∨ (R.2,R.1) ∈ degreeHalfRegions18 := by decide +kernel

lemma degreeDiagramRegionsChecked18 : ∀ R ∈ degreeRegions18,
    ∀ μ : YoungDiagram, μ.card = 18 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP18 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck18 degreeHalfHeight18 degreeHalfWidth18
    degreeHalfCover18

end UniversalTensorSquare
end

end OAI
