import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves19

namespace OAI

/-! Degree Regions 19. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck19 : ∀ h ≤ 8,
    checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) h 19 8 degreeHalfRegions19 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch19_0
  · exact degreeUnionBranch19_1
  · exact degreeUnionBranch19_2
  · exact degreeUnionBranch19_3
  · exact degreeUnionBranch19_4
  · exact degreeUnionBranch19_5
  · exact degreeUnionBranch19_6
  · exact degreeUnionBranch19_7
  · exact degreeUnionBranch19_8

lemma degreeHalfCover19 : ∀ R ∈ degreeRegions19,
    R ∈ degreeHalfRegions19 ∨ (R.2,R.1) ∈ degreeHalfRegions19 := by decide +kernel

lemma degreeDiagramRegionsChecked19 : ∀ R ∈ degreeRegions19,
    ∀ μ : YoungDiagram, μ.card = 19 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP19 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck19 degreeHalfHeight19 degreeHalfWidth19
    degreeHalfCover19

end UniversalTensorSquare
end

end OAI
