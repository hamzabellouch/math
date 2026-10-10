import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.UnionRowChecker
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreePlans19
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeUnionData19

namespace OAI

/-! Degree Leaves 19. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch19_0 : checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) 0 19 8 degreeHalfRegions19 [] = true := by
  decide +kernel

lemma degreeUnionBranch19_1 : checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) 1 19 8 degreeHalfRegions19 [] = true := by
  decide +kernel

lemma degreeUnionBranch19_2 : checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) 2 19 8 degreeHalfRegions19 [] = true := by
  decide +kernel

lemma degreeUnionBranch19_3 : checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) 3 19 8 degreeHalfRegions19 [] = true := by
  decide +kernel

lemma degreeUnionBranch19_4 : checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) 4 19 8 degreeHalfRegions19 [] = true := by
  decide +kernel

lemma degreeUnionBranch19_5 : checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) 5 19 8 degreeHalfRegions19 [] = true := by
  decide +kernel

lemma degreeUnionBranch19_6 : checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) 6 19 8 degreeHalfRegions19 [] = true := by
  decide +kernel

lemma degreeUnionBranch19_7 : checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) 7 19 8 degreeHalfRegions19 [] = true := by
  decide +kernel

lemma degreeUnionBranch19_8 : checkRegionPrefixes (quickResidual 5 2 degreeQs19 degreeTree19) 8 19 8 degreeHalfRegions19 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

end OAI
