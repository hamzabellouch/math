import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves89

namespace OAI

/-! Degree Regions 89. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck89 : ∀ h ≤ 18,
    checkRegionPrefixes (quickResidual 10 17 degreeQs89 degreeTree89) h 89 18 degreeHalfRegions89 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch89_0
  · exact degreeUnionBranch89_1
  · exact degreeUnionBranch89_2
  · exact degreeUnionBranch89_3
  · exact degreeUnionBranch89_4
  · exact degreeUnionBranch89_5
  · exact degreeUnionBranch89_6
  · exact degreeUnionBranch89_7
  · exact degreeUnionBranch89_8
  · exact degreeUnionBranch89_9
  · exact degreeUnionBranch89_10
  · exact degreeUnionBranch89_11
  · exact degreeUnionBranch89_12
  · exact degreeUnionBranch89_13
  · exact degreeUnionBranch89_14
  · exact degreeUnionBranch89_15
  · exact degreeUnionBranch89_16
  · exact degreeUnionBranch89_17
  · exact degreeUnionBranch89_18

lemma degreeHalfCover89 : ∀ R ∈ degreeRegions89,
    R ∈ degreeHalfRegions89 ∨ (R.2,R.1) ∈ degreeHalfRegions89 := by decide +kernel

lemma degreeDiagramRegionsChecked89 : ∀ R ∈ degreeRegions89,
    ∀ μ : YoungDiagram, μ.card = 89 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP89 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck89 degreeHalfHeight89 degreeHalfWidth89
    degreeHalfCover89

end UniversalTensorSquare
end

end OAI
