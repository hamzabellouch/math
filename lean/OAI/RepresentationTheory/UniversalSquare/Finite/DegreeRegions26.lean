import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Support.SplitUnionRowChecker
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves26

namespace OAI

/-! Degree Regions 26. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch26_7 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 7 26 25 degreeHalfRegions26 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 25 at hb
  change 26 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch26_8
  · exact degreeUnionBranch26_9
  · exact degreeUnionBranch26_10
  · exact degreeUnionBranch26_11
  · exact degreeUnionBranch26_12
  · exact degreeUnionBranch26_13
  · exact degreeUnionBranch26_14
  · exact degreeUnionBranch26_15
  · exact degreeUnionBranch26_16
  · exact degreeUnionBranch26_17
  · exact degreeUnionBranch26_18
  · exact degreeUnionBranch26_19
  · exact degreeUnionBranch26_20
  · exact degreeUnionBranch26_21
  · exact degreeUnionBranch26_22
  · exact degreeUnionBranch26_23
  · exact degreeUnionBranch26_24
  · exact degreeUnionBranch26_25
  · exact degreeUnionBranch26_26
  · exact degreeUnionBranch26_27
  · exact degreeUnionBranch26_28
  · exact degreeUnionBranch26_29

lemma degreeUnionBranch26_30 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 8 26 25 degreeHalfRegions26 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 25 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch26_31
  · exact degreeUnionBranch26_32
  · exact degreeUnionBranch26_33
  · exact degreeUnionBranch26_34
  · exact degreeUnionBranch26_35
  · exact degreeUnionBranch26_36
  · exact degreeUnionBranch26_37
  · exact degreeUnionBranch26_38
  · exact degreeUnionBranch26_39
  · exact degreeUnionBranch26_40
  · exact degreeUnionBranch26_41
  · exact degreeUnionBranch26_42
  · exact degreeUnionBranch26_43
  · exact degreeUnionBranch26_44
  · exact degreeUnionBranch26_45
  · exact degreeUnionBranch26_46
  · exact degreeUnionBranch26_47
  · exact degreeUnionBranch26_48
  · exact degreeUnionBranch26_49
  · exact degreeUnionBranch26_50
  · exact degreeUnionBranch26_51
  · exact degreeUnionBranch26_52

lemma degreeUnionBranch26_53 : checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) 9 26 25 degreeHalfRegions26 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 25 at hb
  change 26 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch26_54
  · exact degreeUnionBranch26_55
  · exact degreeUnionBranch26_56
  · exact degreeUnionBranch26_57
  · exact degreeUnionBranch26_58
  · exact degreeUnionBranch26_59
  · exact degreeUnionBranch26_60
  · exact degreeUnionBranch26_61
  · exact degreeUnionBranch26_62
  · exact degreeUnionBranch26_63
  · exact degreeUnionBranch26_64
  · exact degreeUnionBranch26_65
  · exact degreeUnionBranch26_66
  · exact degreeUnionBranch26_67
  · exact degreeUnionBranch26_68
  · exact degreeUnionBranch26_69
  · exact degreeUnionBranch26_70
  · exact degreeUnionBranch26_71
  · exact degreeUnionBranch26_72
  · exact degreeUnionBranch26_73
  · exact degreeUnionBranch26_74
  · exact degreeUnionBranch26_75
  · exact degreeUnionBranch26_76

lemma degreeUnionCheck26 : ∀ h ≤ 25,
    checkRegionPrefixes (quickResidual 4 8 degreeQs26 degreeTree26) h 26 25 degreeHalfRegions26 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch26_0
  · exact degreeUnionBranch26_1
  · exact degreeUnionBranch26_2
  · exact degreeUnionBranch26_3
  · exact degreeUnionBranch26_4
  · exact degreeUnionBranch26_5
  · exact degreeUnionBranch26_6
  · exact degreeUnionBranch26_7
  · exact degreeUnionBranch26_30
  · exact degreeUnionBranch26_53
  · exact degreeUnionBranch26_77
  · exact degreeUnionBranch26_78
  · exact degreeUnionBranch26_79
  · exact degreeUnionBranch26_80
  · exact degreeUnionBranch26_81
  · exact degreeUnionBranch26_82
  · exact degreeUnionBranch26_83
  · exact degreeUnionBranch26_84
  · exact degreeUnionBranch26_85
  · exact degreeUnionBranch26_86
  · exact degreeUnionBranch26_87
  · exact degreeUnionBranch26_88
  · exact degreeUnionBranch26_89
  · exact degreeUnionBranch26_90
  · exact degreeUnionBranch26_91
  · exact degreeUnionBranch26_92

lemma degreeHalfCover26 : ∀ R ∈ degreeRegions26,
    R ∈ degreeHalfRegions26 ∨ (R.2,R.1) ∈ degreeHalfRegions26 := by decide +kernel

lemma degreeDiagramRegionsChecked26 : ∀ R ∈ degreeRegions26,
    ∀ μ : YoungDiagram, μ.card = 26 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP26 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck26 degreeHalfHeight26 degreeHalfWidth26
    degreeHalfCover26

end UniversalTensorSquare
end

end OAI
