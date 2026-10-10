import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves20

namespace OAI

/-! Degree Regions 20. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck20 : ∀ h ≤ 19,
    checkRegionPrefixes (quickResidual 4 5 degreeQs20 degreeTree20) h 20 19 degreeHalfRegions20 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch20_0
  · exact degreeUnionBranch20_1
  · exact degreeUnionBranch20_2
  · exact degreeUnionBranch20_3
  · exact degreeUnionBranch20_4
  · exact degreeUnionBranch20_5
  · exact degreeUnionBranch20_6
  · exact degreeUnionBranch20_7
  · exact degreeUnionBranch20_8
  · exact degreeUnionBranch20_9
  · exact degreeUnionBranch20_10
  · exact degreeUnionBranch20_11
  · exact degreeUnionBranch20_12
  · exact degreeUnionBranch20_13
  · exact degreeUnionBranch20_14
  · exact degreeUnionBranch20_15
  · exact degreeUnionBranch20_16
  · exact degreeUnionBranch20_17
  · exact degreeUnionBranch20_18
  · exact degreeUnionBranch20_19

lemma degreeHalfCover20 : ∀ R ∈ degreeRegions20,
    R ∈ degreeHalfRegions20 ∨ (R.2,R.1) ∈ degreeHalfRegions20 := by decide +kernel

lemma degreeDiagramRegionsChecked20 : ∀ R ∈ degreeRegions20,
    ∀ μ : YoungDiagram, μ.card = 20 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP20 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck20 degreeHalfHeight20 degreeHalfWidth20
    degreeHalfCover20

end UniversalTensorSquare
end

end OAI
