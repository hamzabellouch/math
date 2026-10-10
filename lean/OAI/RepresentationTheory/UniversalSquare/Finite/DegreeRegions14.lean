import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves14

namespace OAI

/-! Degree Regions 14. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck14 : ∀ h ≤ 13,
    checkRegionPrefixes (quickResidual 4 2 degreeQs14 degreeTree14) h 14 13 degreeHalfRegions14 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch14_0
  · exact degreeUnionBranch14_1
  · exact degreeUnionBranch14_2
  · exact degreeUnionBranch14_3
  · exact degreeUnionBranch14_4
  · exact degreeUnionBranch14_5
  · exact degreeUnionBranch14_6
  · exact degreeUnionBranch14_7
  · exact degreeUnionBranch14_8
  · exact degreeUnionBranch14_9
  · exact degreeUnionBranch14_10
  · exact degreeUnionBranch14_11
  · exact degreeUnionBranch14_12
  · exact degreeUnionBranch14_13

lemma degreeHalfCover14 : ∀ R ∈ degreeRegions14,
    R ∈ degreeHalfRegions14 ∨ (R.2,R.1) ∈ degreeHalfRegions14 := by decide +kernel

lemma degreeDiagramRegionsChecked14 : ∀ R ∈ degreeRegions14,
    ∀ μ : YoungDiagram, μ.card = 14 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP14 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck14 degreeHalfHeight14 degreeHalfWidth14
    degreeHalfCover14

end UniversalTensorSquare
end

end OAI
