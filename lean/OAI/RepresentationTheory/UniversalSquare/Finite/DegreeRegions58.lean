import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Support.SplitUnionRowChecker
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves58

namespace OAI

/-! Degree Regions 58. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch58_25 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 37 9 degreeUnionState58_25 [9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 37 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_26
  · exact degreeUnionBranch58_27
  · exact degreeUnionBranch58_28
  · exact degreeUnionBranch58_29
  · exact degreeUnionBranch58_30
  · exact degreeUnionBranch58_31

lemma degreeUnionBranch58_20 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 46 12 degreeUnionState58_20 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 12 at hb
  change 46 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_21
  · exact degreeUnionBranch58_22
  · exact degreeUnionBranch58_23
  · exact degreeUnionBranch58_24
  · exact degreeUnionBranch58_25
  · exact degreeUnionBranch58_32
  · exact degreeUnionBranch58_33
  · exact degreeUnionBranch58_34

lemma degreeUnionBranch58_39 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 10 37 8 degreeUnionState58_39 [8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 37 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_40
  · exact degreeUnionBranch58_41
  · exact degreeUnionBranch58_42
  · exact degreeUnionBranch58_43
  · exact degreeUnionBranch58_44

lemma degreeUnionBranch58_35 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 45 13 degreeUnionState58_35 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 13 at hb
  change 45 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_36
  · exact degreeUnionBranch58_37
  · exact degreeUnionBranch58_38
  · exact degreeUnionBranch58_39
  · exact degreeUnionBranch58_45
  · exact degreeUnionBranch58_46
  · exact degreeUnionBranch58_47
  · exact degreeUnionBranch58_48
  · exact degreeUnionBranch58_49

lemma degreeUnionBranch58_50 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 11 44 14 degreeUnionState58_50 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 44 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_51
  · exact degreeUnionBranch58_52
  · exact degreeUnionBranch58_53
  · exact degreeUnionBranch58_54
  · exact degreeUnionBranch58_55
  · exact degreeUnionBranch58_56
  · exact degreeUnionBranch58_57
  · exact degreeUnionBranch58_58
  · exact degreeUnionBranch58_59
  · exact degreeUnionBranch58_60
  · exact degreeUnionBranch58_61

lemma degreeUnionBranch58_12 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 58 14 degreeHalfRegions58 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 58 ≤ 12*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_13
  · exact degreeUnionBranch58_14
  · exact degreeUnionBranch58_15
  · exact degreeUnionBranch58_16
  · exact degreeUnionBranch58_17
  · exact degreeUnionBranch58_18
  · exact degreeUnionBranch58_19
  · exact degreeUnionBranch58_20
  · exact degreeUnionBranch58_35
  · exact degreeUnionBranch58_50

lemma degreeUnionBranch58_70 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 46 12 degreeUnionState58_70 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 46 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_71
  · exact degreeUnionBranch58_72
  · exact degreeUnionBranch58_73
  · exact degreeUnionBranch58_74
  · exact degreeUnionBranch58_75
  · exact degreeUnionBranch58_76
  · exact degreeUnionBranch58_77
  · exact degreeUnionBranch58_78
  · exact degreeUnionBranch58_79

lemma degreeUnionBranch58_80 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 12 45 13 degreeUnionState58_80 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 45 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_81
  · exact degreeUnionBranch58_82
  · exact degreeUnionBranch58_83
  · exact degreeUnionBranch58_84
  · exact degreeUnionBranch58_85
  · exact degreeUnionBranch58_86
  · exact degreeUnionBranch58_87
  · exact degreeUnionBranch58_88
  · exact degreeUnionBranch58_89
  · exact degreeUnionBranch58_90

lemma degreeUnionBranch58_62 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 58 14 degreeHalfRegions58 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 58 ≤ 13*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_63
  · exact degreeUnionBranch58_64
  · exact degreeUnionBranch58_65
  · exact degreeUnionBranch58_66
  · exact degreeUnionBranch58_67
  · exact degreeUnionBranch58_68
  · exact degreeUnionBranch58_69
  · exact degreeUnionBranch58_70
  · exact degreeUnionBranch58_80
  · exact degreeUnionBranch58_91

lemma degreeUnionBranch58_100 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 13 46 12 degreeUnionState58_100 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 46 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_101
  · exact degreeUnionBranch58_102
  · exact degreeUnionBranch58_103
  · exact degreeUnionBranch58_104
  · exact degreeUnionBranch58_105
  · exact degreeUnionBranch58_106
  · exact degreeUnionBranch58_107
  · exact degreeUnionBranch58_108
  · exact degreeUnionBranch58_109

lemma degreeUnionBranch58_92 : checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) 14 58 14 degreeHalfRegions58 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 58 ≤ 14*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch58_93
  · exact degreeUnionBranch58_94
  · exact degreeUnionBranch58_95
  · exact degreeUnionBranch58_96
  · exact degreeUnionBranch58_97
  · exact degreeUnionBranch58_98
  · exact degreeUnionBranch58_99
  · exact degreeUnionBranch58_100
  · exact degreeUnionBranch58_110
  · exact degreeUnionBranch58_111

lemma degreeUnionCheck58 : ∀ h ≤ 24,
    checkRegionPrefixes (quickResidual 8 11 degreeQs58 degreeTree58) h 58 14 degreeHalfRegions58 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch58_0
  · exact degreeUnionBranch58_1
  · exact degreeUnionBranch58_2
  · exact degreeUnionBranch58_3
  · exact degreeUnionBranch58_4
  · exact degreeUnionBranch58_5
  · exact degreeUnionBranch58_6
  · exact degreeUnionBranch58_7
  · exact degreeUnionBranch58_8
  · exact degreeUnionBranch58_9
  · exact degreeUnionBranch58_10
  · exact degreeUnionBranch58_11
  · exact degreeUnionBranch58_12
  · exact degreeUnionBranch58_62
  · exact degreeUnionBranch58_92
  · exact degreeUnionBranch58_112
  · exact degreeUnionBranch58_113
  · exact degreeUnionBranch58_114
  · exact degreeUnionBranch58_115
  · exact degreeUnionBranch58_116
  · exact degreeUnionBranch58_117
  · exact degreeUnionBranch58_118
  · exact degreeUnionBranch58_119
  · exact degreeUnionBranch58_120
  · exact degreeUnionBranch58_121

lemma degreeHalfCover58 : ∀ R ∈ degreeRegions58,
    R ∈ degreeHalfRegions58 ∨ (R.2,R.1) ∈ degreeHalfRegions58 := by decide +kernel

lemma degreeDiagramRegionsChecked58 : ∀ R ∈ degreeRegions58,
    ∀ μ : YoungDiagram, μ.card = 58 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP58 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck58 degreeHalfHeight58 degreeHalfWidth58
    degreeHalfCover58

end UniversalTensorSquare
end

end OAI
