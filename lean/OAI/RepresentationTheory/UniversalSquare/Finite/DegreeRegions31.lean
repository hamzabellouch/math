import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Support.SplitUnionRowChecker
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves31

namespace OAI

/-! Degree Regions 31. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch31_8 : checkRegionPrefixes (quickResidual 6 5 degreeQs31 degreeTree31) 8 31 30 degreeHalfRegions31 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 30 at hb
  change 31 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch31_9
  · exact degreeUnionBranch31_10
  · exact degreeUnionBranch31_11
  · exact degreeUnionBranch31_12
  · exact degreeUnionBranch31_13
  · exact degreeUnionBranch31_14
  · exact degreeUnionBranch31_15
  · exact degreeUnionBranch31_16
  · exact degreeUnionBranch31_17
  · exact degreeUnionBranch31_18
  · exact degreeUnionBranch31_19
  · exact degreeUnionBranch31_20
  · exact degreeUnionBranch31_21
  · exact degreeUnionBranch31_22
  · exact degreeUnionBranch31_23
  · exact degreeUnionBranch31_24
  · exact degreeUnionBranch31_25
  · exact degreeUnionBranch31_26
  · exact degreeUnionBranch31_27
  · exact degreeUnionBranch31_28
  · exact degreeUnionBranch31_29
  · exact degreeUnionBranch31_30
  · exact degreeUnionBranch31_31
  · exact degreeUnionBranch31_32
  · exact degreeUnionBranch31_33
  · exact degreeUnionBranch31_34
  · exact degreeUnionBranch31_35

lemma degreeUnionBranch31_36 : checkRegionPrefixes (quickResidual 6 5 degreeQs31 degreeTree31) 9 31 30 degreeHalfRegions31 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 30 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch31_37
  · exact degreeUnionBranch31_38
  · exact degreeUnionBranch31_39
  · exact degreeUnionBranch31_40
  · exact degreeUnionBranch31_41
  · exact degreeUnionBranch31_42
  · exact degreeUnionBranch31_43
  · exact degreeUnionBranch31_44
  · exact degreeUnionBranch31_45
  · exact degreeUnionBranch31_46
  · exact degreeUnionBranch31_47
  · exact degreeUnionBranch31_48
  · exact degreeUnionBranch31_49
  · exact degreeUnionBranch31_50
  · exact degreeUnionBranch31_51
  · exact degreeUnionBranch31_52
  · exact degreeUnionBranch31_53
  · exact degreeUnionBranch31_54
  · exact degreeUnionBranch31_55
  · exact degreeUnionBranch31_56
  · exact degreeUnionBranch31_57
  · exact degreeUnionBranch31_58
  · exact degreeUnionBranch31_59
  · exact degreeUnionBranch31_60
  · exact degreeUnionBranch31_61
  · exact degreeUnionBranch31_62
  · exact degreeUnionBranch31_63

lemma degreeUnionBranch31_64 : checkRegionPrefixes (quickResidual 6 5 degreeQs31 degreeTree31) 10 31 30 degreeHalfRegions31 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 30 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch31_65
  · exact degreeUnionBranch31_66
  · exact degreeUnionBranch31_67
  · exact degreeUnionBranch31_68
  · exact degreeUnionBranch31_69
  · exact degreeUnionBranch31_70
  · exact degreeUnionBranch31_71
  · exact degreeUnionBranch31_72
  · exact degreeUnionBranch31_73
  · exact degreeUnionBranch31_74
  · exact degreeUnionBranch31_75
  · exact degreeUnionBranch31_76
  · exact degreeUnionBranch31_77
  · exact degreeUnionBranch31_78
  · exact degreeUnionBranch31_79
  · exact degreeUnionBranch31_80
  · exact degreeUnionBranch31_81
  · exact degreeUnionBranch31_82
  · exact degreeUnionBranch31_83
  · exact degreeUnionBranch31_84
  · exact degreeUnionBranch31_85
  · exact degreeUnionBranch31_86
  · exact degreeUnionBranch31_87
  · exact degreeUnionBranch31_88
  · exact degreeUnionBranch31_89
  · exact degreeUnionBranch31_90
  · exact degreeUnionBranch31_91

lemma degreeUnionCheck31 : ∀ h ≤ 10,
    checkRegionPrefixes (quickResidual 6 5 degreeQs31 degreeTree31) h 31 30 degreeHalfRegions31 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch31_0
  · exact degreeUnionBranch31_1
  · exact degreeUnionBranch31_2
  · exact degreeUnionBranch31_3
  · exact degreeUnionBranch31_4
  · exact degreeUnionBranch31_5
  · exact degreeUnionBranch31_6
  · exact degreeUnionBranch31_7
  · exact degreeUnionBranch31_8
  · exact degreeUnionBranch31_36
  · exact degreeUnionBranch31_64

lemma degreeHalfCover31 : ∀ R ∈ degreeRegions31,
    R ∈ degreeHalfRegions31 ∨ (R.2,R.1) ∈ degreeHalfRegions31 := by decide +kernel

lemma degreeDiagramRegionsChecked31 : ∀ R ∈ degreeRegions31,
    ∀ μ : YoungDiagram, μ.card = 31 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP31 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck31 degreeHalfHeight31 degreeHalfWidth31
    degreeHalfCover31

end UniversalTensorSquare
end

end OAI
