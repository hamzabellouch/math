import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Support.SplitUnionRowChecker
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves35

namespace OAI

/-! Degree Regions 35. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch35_13 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 26 9 degreeUnionState35_13 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 26 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_14
  · exact degreeUnionBranch35_15
  · exact degreeUnionBranch35_16
  · exact degreeUnionBranch35_17
  · exact degreeUnionBranch35_18
  · exact degreeUnionBranch35_19

lemma degreeUnionBranch35_20 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 7 25 10 degreeUnionState35_20 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 25 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_21
  · exact degreeUnionBranch35_22
  · exact degreeUnionBranch35_23
  · exact degreeUnionBranch35_24
  · exact degreeUnionBranch35_25
  · exact degreeUnionBranch35_26
  · exact degreeUnionBranch35_27

lemma degreeUnionBranch35_8 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 35 34 degreeHalfRegions35 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 34 at hb
  change 35 ≤ 8*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_9
  · exact degreeUnionBranch35_10
  · exact degreeUnionBranch35_11
  · exact degreeUnionBranch35_12
  · exact degreeUnionBranch35_13
  · exact degreeUnionBranch35_20
  · exact degreeUnionBranch35_28
  · exact degreeUnionBranch35_29
  · exact degreeUnionBranch35_30
  · exact degreeUnionBranch35_31
  · exact degreeUnionBranch35_32
  · exact degreeUnionBranch35_33
  · exact degreeUnionBranch35_34
  · exact degreeUnionBranch35_35
  · exact degreeUnionBranch35_36
  · exact degreeUnionBranch35_37
  · exact degreeUnionBranch35_38
  · exact degreeUnionBranch35_39
  · exact degreeUnionBranch35_40
  · exact degreeUnionBranch35_41
  · exact degreeUnionBranch35_42
  · exact degreeUnionBranch35_43
  · exact degreeUnionBranch35_44
  · exact degreeUnionBranch35_45
  · exact degreeUnionBranch35_46
  · exact degreeUnionBranch35_47
  · exact degreeUnionBranch35_48
  · exact degreeUnionBranch35_49
  · exact degreeUnionBranch35_50
  · exact degreeUnionBranch35_51

lemma degreeUnionBranch35_57 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 27 8 degreeUnionState35_57 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 27 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_58
  · exact degreeUnionBranch35_59
  · exact degreeUnionBranch35_60
  · exact degreeUnionBranch35_61
  · exact degreeUnionBranch35_62

lemma degreeUnionBranch35_63 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 26 9 degreeUnionState35_63 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_64
  · exact degreeUnionBranch35_65
  · exact degreeUnionBranch35_66
  · exact degreeUnionBranch35_67
  · exact degreeUnionBranch35_68
  · exact degreeUnionBranch35_69

lemma degreeUnionBranch35_70 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 8 25 10 degreeUnionState35_70 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 25 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_71
  · exact degreeUnionBranch35_72
  · exact degreeUnionBranch35_73
  · exact degreeUnionBranch35_74
  · exact degreeUnionBranch35_75
  · exact degreeUnionBranch35_76
  · exact degreeUnionBranch35_77

lemma degreeUnionBranch35_52 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 9 35 34 degreeHalfRegions35 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 34 at hb
  change 35 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_53
  · exact degreeUnionBranch35_54
  · exact degreeUnionBranch35_55
  · exact degreeUnionBranch35_56
  · exact degreeUnionBranch35_57
  · exact degreeUnionBranch35_63
  · exact degreeUnionBranch35_70
  · exact degreeUnionBranch35_78
  · exact degreeUnionBranch35_79
  · exact degreeUnionBranch35_80
  · exact degreeUnionBranch35_81
  · exact degreeUnionBranch35_82
  · exact degreeUnionBranch35_83
  · exact degreeUnionBranch35_84
  · exact degreeUnionBranch35_85
  · exact degreeUnionBranch35_86
  · exact degreeUnionBranch35_87
  · exact degreeUnionBranch35_88
  · exact degreeUnionBranch35_89
  · exact degreeUnionBranch35_90
  · exact degreeUnionBranch35_91
  · exact degreeUnionBranch35_92
  · exact degreeUnionBranch35_93
  · exact degreeUnionBranch35_94
  · exact degreeUnionBranch35_95
  · exact degreeUnionBranch35_96
  · exact degreeUnionBranch35_97
  · exact degreeUnionBranch35_98
  · exact degreeUnionBranch35_99
  · exact degreeUnionBranch35_100
  · exact degreeUnionBranch35_101

lemma degreeUnionBranch35_107 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 9 27 8 degreeUnionState35_107 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 27 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_108
  · exact degreeUnionBranch35_109
  · exact degreeUnionBranch35_110
  · exact degreeUnionBranch35_111
  · exact degreeUnionBranch35_112
  · exact degreeUnionBranch35_113

lemma degreeUnionBranch35_114 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 9 26 9 degreeUnionState35_114 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 26 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_115
  · exact degreeUnionBranch35_116
  · exact degreeUnionBranch35_117
  · exact degreeUnionBranch35_118
  · exact degreeUnionBranch35_119
  · exact degreeUnionBranch35_120
  · exact degreeUnionBranch35_121

lemma degreeUnionBranch35_122 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 9 25 10 degreeUnionState35_122 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 25 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_123
  · exact degreeUnionBranch35_124
  · exact degreeUnionBranch35_125
  · exact degreeUnionBranch35_126
  · exact degreeUnionBranch35_127
  · exact degreeUnionBranch35_128
  · exact degreeUnionBranch35_129
  · exact degreeUnionBranch35_130

lemma degreeUnionBranch35_102 : checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) 10 35 34 degreeHalfRegions35 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 34 at hb
  change 35 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch35_103
  · exact degreeUnionBranch35_104
  · exact degreeUnionBranch35_105
  · exact degreeUnionBranch35_106
  · exact degreeUnionBranch35_107
  · exact degreeUnionBranch35_114
  · exact degreeUnionBranch35_122
  · exact degreeUnionBranch35_131
  · exact degreeUnionBranch35_132
  · exact degreeUnionBranch35_133
  · exact degreeUnionBranch35_134
  · exact degreeUnionBranch35_135
  · exact degreeUnionBranch35_136
  · exact degreeUnionBranch35_137
  · exact degreeUnionBranch35_138
  · exact degreeUnionBranch35_139
  · exact degreeUnionBranch35_140
  · exact degreeUnionBranch35_141
  · exact degreeUnionBranch35_142
  · exact degreeUnionBranch35_143
  · exact degreeUnionBranch35_144
  · exact degreeUnionBranch35_145
  · exact degreeUnionBranch35_146
  · exact degreeUnionBranch35_147
  · exact degreeUnionBranch35_148
  · exact degreeUnionBranch35_149
  · exact degreeUnionBranch35_150
  · exact degreeUnionBranch35_151
  · exact degreeUnionBranch35_152
  · exact degreeUnionBranch35_153
  · exact degreeUnionBranch35_154

lemma degreeUnionCheck35 : ∀ h ≤ 15,
    checkRegionPrefixes (quickResidual 6 7 degreeQs35 degreeTree35) h 35 34 degreeHalfRegions35 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch35_0
  · exact degreeUnionBranch35_1
  · exact degreeUnionBranch35_2
  · exact degreeUnionBranch35_3
  · exact degreeUnionBranch35_4
  · exact degreeUnionBranch35_5
  · exact degreeUnionBranch35_6
  · exact degreeUnionBranch35_7
  · exact degreeUnionBranch35_8
  · exact degreeUnionBranch35_52
  · exact degreeUnionBranch35_102
  · exact degreeUnionBranch35_155
  · exact degreeUnionBranch35_156
  · exact degreeUnionBranch35_157
  · exact degreeUnionBranch35_158
  · exact degreeUnionBranch35_159

lemma degreeHalfCover35 : ∀ R ∈ degreeRegions35,
    R ∈ degreeHalfRegions35 ∨ (R.2,R.1) ∈ degreeHalfRegions35 := by decide +kernel

lemma degreeDiagramRegionsChecked35 : ∀ R ∈ degreeRegions35,
    ∀ μ : YoungDiagram, μ.card = 35 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP35 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck35 degreeHalfHeight35 degreeHalfWidth35
    degreeHalfCover35

end UniversalTensorSquare
end

end OAI
