import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Support.SplitUnionRowChecker
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves62

namespace OAI

/-! Degree Regions 62. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch62_18 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 50 12 degreeUnionState62_18 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 5 ≤ a at ha
  change a ≤ 12 at hb
  change 50 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_19
  · exact degreeUnionBranch62_20
  · exact degreeUnionBranch62_21
  · exact degreeUnionBranch62_22
  · exact degreeUnionBranch62_23
  · exact degreeUnionBranch62_24
  · exact degreeUnionBranch62_25
  · exact degreeUnionBranch62_26

lemma degreeUnionBranch62_27 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 49 13 degreeUnionState62_27 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 13 at hb
  change 49 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_28
  · exact degreeUnionBranch62_29
  · exact degreeUnionBranch62_30
  · exact degreeUnionBranch62_31
  · exact degreeUnionBranch62_32
  · exact degreeUnionBranch62_33
  · exact degreeUnionBranch62_34
  · exact degreeUnionBranch62_35
  · exact degreeUnionBranch62_36

lemma degreeUnionBranch62_37 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 48 14 degreeUnionState62_37 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 48 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_38
  · exact degreeUnionBranch62_39
  · exact degreeUnionBranch62_40
  · exact degreeUnionBranch62_41
  · exact degreeUnionBranch62_42
  · exact degreeUnionBranch62_43
  · exact degreeUnionBranch62_44
  · exact degreeUnionBranch62_45
  · exact degreeUnionBranch62_46
  · exact degreeUnionBranch62_47

lemma degreeUnionBranch62_11 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 62 28 degreeHalfRegions62 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 5 ≤ a at ha
  change a ≤ 28 at hb
  change 62 ≤ 11*a at hn
  have hlo : 6 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_12
  · exact degreeUnionBranch62_13
  · exact degreeUnionBranch62_14
  · exact degreeUnionBranch62_15
  · exact degreeUnionBranch62_16
  · exact degreeUnionBranch62_17
  · exact degreeUnionBranch62_18
  · exact degreeUnionBranch62_27
  · exact degreeUnionBranch62_37
  · exact degreeUnionBranch62_48
  · exact degreeUnionBranch62_49
  · exact degreeUnionBranch62_50
  · exact degreeUnionBranch62_51
  · exact degreeUnionBranch62_52
  · exact degreeUnionBranch62_53
  · exact degreeUnionBranch62_54
  · exact degreeUnionBranch62_55
  · exact degreeUnionBranch62_56
  · exact degreeUnionBranch62_57
  · exact degreeUnionBranch62_58
  · exact degreeUnionBranch62_59
  · exact degreeUnionBranch62_60
  · exact degreeUnionBranch62_61

lemma degreeUnionBranch62_79 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 10 degreeUnionState62_79 [10,10,10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_80
  · exact degreeUnionBranch62_81
  · exact degreeUnionBranch62_82
  · exact degreeUnionBranch62_83
  · exact degreeUnionBranch62_84
  · exact degreeUnionBranch62_85
  · exact degreeUnionBranch62_86

lemma degreeUnionBranch62_73 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 42 10 degreeUnionState62_73 [10,10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 42 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_74
  · exact degreeUnionBranch62_75
  · exact degreeUnionBranch62_76
  · exact degreeUnionBranch62_77
  · exact degreeUnionBranch62_78
  · exact degreeUnionBranch62_79

lemma degreeUnionBranch62_67 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 52 10 degreeUnionState62_67 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 52 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_68
  · exact degreeUnionBranch62_69
  · exact degreeUnionBranch62_70
  · exact degreeUnionBranch62_71
  · exact degreeUnionBranch62_72
  · exact degreeUnionBranch62_73

lemma degreeUnionBranch62_99 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 10 degreeUnionState62_99 [10,10,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_100
  · exact degreeUnionBranch62_101
  · exact degreeUnionBranch62_102
  · exact degreeUnionBranch62_103
  · exact degreeUnionBranch62_104
  · exact degreeUnionBranch62_105
  · exact degreeUnionBranch62_106

lemma degreeUnionBranch62_93 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 41 10 degreeUnionState62_93 [10,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 41 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_94
  · exact degreeUnionBranch62_95
  · exact degreeUnionBranch62_96
  · exact degreeUnionBranch62_97
  · exact degreeUnionBranch62_98
  · exact degreeUnionBranch62_99

lemma degreeUnionBranch62_114 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 10 degreeUnionState62_114 [10,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_115
  · exact degreeUnionBranch62_116
  · exact degreeUnionBranch62_117
  · exact degreeUnionBranch62_118
  · exact degreeUnionBranch62_119
  · exact degreeUnionBranch62_120
  · exact degreeUnionBranch62_121

lemma degreeUnionBranch62_122 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 11 degreeUnionState62_122 [11,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_123
  · exact degreeUnionBranch62_124
  · exact degreeUnionBranch62_125
  · exact degreeUnionBranch62_126
  · exact degreeUnionBranch62_127
  · exact degreeUnionBranch62_128
  · exact degreeUnionBranch62_129
  · exact degreeUnionBranch62_130

lemma degreeUnionBranch62_107 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 40 11 degreeUnionState62_107 [11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 11 at hb
  change 40 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_108
  · exact degreeUnionBranch62_109
  · exact degreeUnionBranch62_110
  · exact degreeUnionBranch62_111
  · exact degreeUnionBranch62_112
  · exact degreeUnionBranch62_113
  · exact degreeUnionBranch62_114
  · exact degreeUnionBranch62_122

lemma degreeUnionBranch62_87 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 51 11 degreeUnionState62_87 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 11 at hb
  change 51 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_88
  · exact degreeUnionBranch62_89
  · exact degreeUnionBranch62_90
  · exact degreeUnionBranch62_91
  · exact degreeUnionBranch62_92
  · exact degreeUnionBranch62_93
  · exact degreeUnionBranch62_107

lemma degreeUnionBranch62_134 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 43 7 degreeUnionState62_134 [7,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 7 at hb
  change 43 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_135
  · exact degreeUnionBranch62_136
  · exact degreeUnionBranch62_137

lemma degreeUnionBranch62_141 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 35 7 degreeUnionState62_141 [7,8,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 35 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_142
  · exact degreeUnionBranch62_143
  · exact degreeUnionBranch62_144
  · exact degreeUnionBranch62_145

lemma degreeUnionBranch62_146 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 8 degreeUnionState62_146 [8,8,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 34 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_147
  · exact degreeUnionBranch62_148
  · exact degreeUnionBranch62_149
  · exact degreeUnionBranch62_150
  · exact degreeUnionBranch62_151

lemma degreeUnionBranch62_138 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 42 8 degreeUnionState62_138 [8,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 8 at hb
  change 42 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_139
  · exact degreeUnionBranch62_140
  · exact degreeUnionBranch62_141
  · exact degreeUnionBranch62_146

lemma degreeUnionBranch62_155 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 7 degreeUnionState62_155 [7,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 34 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_156
  · exact degreeUnionBranch62_157
  · exact degreeUnionBranch62_158
  · exact degreeUnionBranch62_159

lemma degreeUnionBranch62_160 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 8 degreeUnionState62_160 [8,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 33 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_161
  · exact degreeUnionBranch62_162
  · exact degreeUnionBranch62_163
  · exact degreeUnionBranch62_164
  · exact degreeUnionBranch62_165

lemma degreeUnionBranch62_166 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 9 degreeUnionState62_166 [9,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_167
  · exact degreeUnionBranch62_168
  · exact degreeUnionBranch62_169
  · exact degreeUnionBranch62_170
  · exact degreeUnionBranch62_171
  · exact degreeUnionBranch62_172

lemma degreeUnionBranch62_152 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 41 9 degreeUnionState62_152 [9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 9 at hb
  change 41 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_153
  · exact degreeUnionBranch62_154
  · exact degreeUnionBranch62_155
  · exact degreeUnionBranch62_160
  · exact degreeUnionBranch62_166

lemma degreeUnionBranch62_177 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 7 degreeUnionState62_177 [7,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 33 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_178
  · exact degreeUnionBranch62_179
  · exact degreeUnionBranch62_180
  · exact degreeUnionBranch62_181

lemma degreeUnionBranch62_182 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 8 degreeUnionState62_182 [8,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_183
  · exact degreeUnionBranch62_184
  · exact degreeUnionBranch62_185
  · exact degreeUnionBranch62_186
  · exact degreeUnionBranch62_187

lemma degreeUnionBranch62_188 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 9 degreeUnionState62_188 [9,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_189
  · exact degreeUnionBranch62_190
  · exact degreeUnionBranch62_191
  · exact degreeUnionBranch62_192
  · exact degreeUnionBranch62_193
  · exact degreeUnionBranch62_194

lemma degreeUnionBranch62_195 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 10 degreeUnionState62_195 [10,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_196
  · exact degreeUnionBranch62_197
  · exact degreeUnionBranch62_198
  · exact degreeUnionBranch62_199
  · exact degreeUnionBranch62_200
  · exact degreeUnionBranch62_201
  · exact degreeUnionBranch62_202

lemma degreeUnionBranch62_173 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 40 10 degreeUnionState62_173 [10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 40 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_174
  · exact degreeUnionBranch62_175
  · exact degreeUnionBranch62_176
  · exact degreeUnionBranch62_177
  · exact degreeUnionBranch62_182
  · exact degreeUnionBranch62_188
  · exact degreeUnionBranch62_195

lemma degreeUnionBranch62_207 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 7 degreeUnionState62_207 [7,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_208
  · exact degreeUnionBranch62_209
  · exact degreeUnionBranch62_210
  · exact degreeUnionBranch62_211

lemma degreeUnionBranch62_212 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 8 degreeUnionState62_212 [8,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_213
  · exact degreeUnionBranch62_214
  · exact degreeUnionBranch62_215
  · exact degreeUnionBranch62_216
  · exact degreeUnionBranch62_217

lemma degreeUnionBranch62_218 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 9 degreeUnionState62_218 [9,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_219
  · exact degreeUnionBranch62_220
  · exact degreeUnionBranch62_221
  · exact degreeUnionBranch62_222
  · exact degreeUnionBranch62_223
  · exact degreeUnionBranch62_224

lemma degreeUnionBranch62_225 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 10 degreeUnionState62_225 [10,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_226
  · exact degreeUnionBranch62_227
  · exact degreeUnionBranch62_228
  · exact degreeUnionBranch62_229
  · exact degreeUnionBranch62_230
  · exact degreeUnionBranch62_231
  · exact degreeUnionBranch62_232

lemma degreeUnionBranch62_203 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 39 11 degreeUnionState62_203 [11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 39 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_204
  · exact degreeUnionBranch62_205
  · exact degreeUnionBranch62_206
  · exact degreeUnionBranch62_207
  · exact degreeUnionBranch62_212
  · exact degreeUnionBranch62_218
  · exact degreeUnionBranch62_225
  · exact degreeUnionBranch62_233

lemma degreeUnionBranch62_238 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 7 degreeUnionState62_238 [7,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_239
  · exact degreeUnionBranch62_240
  · exact degreeUnionBranch62_241
  · exact degreeUnionBranch62_242

lemma degreeUnionBranch62_243 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 8 degreeUnionState62_243 [8,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_244
  · exact degreeUnionBranch62_245
  · exact degreeUnionBranch62_246
  · exact degreeUnionBranch62_247
  · exact degreeUnionBranch62_248

lemma degreeUnionBranch62_249 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 9 degreeUnionState62_249 [9,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_250
  · exact degreeUnionBranch62_251
  · exact degreeUnionBranch62_252
  · exact degreeUnionBranch62_253
  · exact degreeUnionBranch62_254
  · exact degreeUnionBranch62_255

lemma degreeUnionBranch62_234 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 38 12 degreeUnionState62_234 [12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 38 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_235
  · exact degreeUnionBranch62_236
  · exact degreeUnionBranch62_237
  · exact degreeUnionBranch62_238
  · exact degreeUnionBranch62_243
  · exact degreeUnionBranch62_249
  · exact degreeUnionBranch62_256
  · exact degreeUnionBranch62_257
  · exact degreeUnionBranch62_258

lemma degreeUnionBranch62_131 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 50 12 degreeUnionState62_131 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 12 at hb
  change 50 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_132
  · exact degreeUnionBranch62_133
  · exact degreeUnionBranch62_134
  · exact degreeUnionBranch62_138
  · exact degreeUnionBranch62_152
  · exact degreeUnionBranch62_173
  · exact degreeUnionBranch62_203
  · exact degreeUnionBranch62_234

lemma degreeUnionBranch62_265 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 35 7 degreeUnionState62_265 [7,7,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 35 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_266
  · exact degreeUnionBranch62_267
  · exact degreeUnionBranch62_268
  · exact degreeUnionBranch62_269

lemma degreeUnionBranch62_262 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 42 7 degreeUnionState62_262 [7,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 7 at hb
  change 42 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_263
  · exact degreeUnionBranch62_264
  · exact degreeUnionBranch62_265

lemma degreeUnionBranch62_273 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 7 degreeUnionState62_273 [7,8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 34 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_274
  · exact degreeUnionBranch62_275
  · exact degreeUnionBranch62_276
  · exact degreeUnionBranch62_277

lemma degreeUnionBranch62_278 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 8 degreeUnionState62_278 [8,8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 33 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_279
  · exact degreeUnionBranch62_280
  · exact degreeUnionBranch62_281
  · exact degreeUnionBranch62_282
  · exact degreeUnionBranch62_283

lemma degreeUnionBranch62_270 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 41 8 degreeUnionState62_270 [8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 8 at hb
  change 41 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_271
  · exact degreeUnionBranch62_272
  · exact degreeUnionBranch62_273
  · exact degreeUnionBranch62_278

lemma degreeUnionBranch62_288 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 7 degreeUnionState62_288 [7,9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 33 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_289
  · exact degreeUnionBranch62_290
  · exact degreeUnionBranch62_291
  · exact degreeUnionBranch62_292

lemma degreeUnionBranch62_293 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 8 degreeUnionState62_293 [8,9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_294
  · exact degreeUnionBranch62_295
  · exact degreeUnionBranch62_296
  · exact degreeUnionBranch62_297
  · exact degreeUnionBranch62_298

lemma degreeUnionBranch62_299 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 9 degreeUnionState62_299 [9,9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_300
  · exact degreeUnionBranch62_301
  · exact degreeUnionBranch62_302
  · exact degreeUnionBranch62_303
  · exact degreeUnionBranch62_304
  · exact degreeUnionBranch62_305

lemma degreeUnionBranch62_284 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 40 9 degreeUnionState62_284 [9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 9 at hb
  change 40 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_285
  · exact degreeUnionBranch62_286
  · exact degreeUnionBranch62_287
  · exact degreeUnionBranch62_288
  · exact degreeUnionBranch62_293
  · exact degreeUnionBranch62_299

lemma degreeUnionBranch62_310 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 7 degreeUnionState62_310 [7,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_311
  · exact degreeUnionBranch62_312
  · exact degreeUnionBranch62_313
  · exact degreeUnionBranch62_314

lemma degreeUnionBranch62_315 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 8 degreeUnionState62_315 [8,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_316
  · exact degreeUnionBranch62_317
  · exact degreeUnionBranch62_318
  · exact degreeUnionBranch62_319
  · exact degreeUnionBranch62_320

lemma degreeUnionBranch62_321 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 9 degreeUnionState62_321 [9,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_322
  · exact degreeUnionBranch62_323
  · exact degreeUnionBranch62_324
  · exact degreeUnionBranch62_325
  · exact degreeUnionBranch62_326
  · exact degreeUnionBranch62_327

lemma degreeUnionBranch62_328 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 10 degreeUnionState62_328 [10,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_329
  · exact degreeUnionBranch62_330
  · exact degreeUnionBranch62_331
  · exact degreeUnionBranch62_332
  · exact degreeUnionBranch62_333
  · exact degreeUnionBranch62_334
  · exact degreeUnionBranch62_335

lemma degreeUnionBranch62_306 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 39 10 degreeUnionState62_306 [10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 39 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_307
  · exact degreeUnionBranch62_308
  · exact degreeUnionBranch62_309
  · exact degreeUnionBranch62_310
  · exact degreeUnionBranch62_315
  · exact degreeUnionBranch62_321
  · exact degreeUnionBranch62_328

lemma degreeUnionBranch62_340 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 7 degreeUnionState62_340 [7,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_341
  · exact degreeUnionBranch62_342
  · exact degreeUnionBranch62_343
  · exact degreeUnionBranch62_344

lemma degreeUnionBranch62_345 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 8 degreeUnionState62_345 [8,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_346
  · exact degreeUnionBranch62_347
  · exact degreeUnionBranch62_348
  · exact degreeUnionBranch62_349
  · exact degreeUnionBranch62_350

lemma degreeUnionBranch62_351 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 9 degreeUnionState62_351 [9,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_352
  · exact degreeUnionBranch62_353
  · exact degreeUnionBranch62_354
  · exact degreeUnionBranch62_355
  · exact degreeUnionBranch62_356
  · exact degreeUnionBranch62_357

lemma degreeUnionBranch62_336 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 38 11 degreeUnionState62_336 [11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 38 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_337
  · exact degreeUnionBranch62_338
  · exact degreeUnionBranch62_339
  · exact degreeUnionBranch62_340
  · exact degreeUnionBranch62_345
  · exact degreeUnionBranch62_351
  · exact degreeUnionBranch62_358
  · exact degreeUnionBranch62_359

lemma degreeUnionBranch62_364 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 7 degreeUnionState62_364 [7,12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_365
  · exact degreeUnionBranch62_366
  · exact degreeUnionBranch62_367
  · exact degreeUnionBranch62_368

lemma degreeUnionBranch62_369 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 8 degreeUnionState62_369 [8,12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_370
  · exact degreeUnionBranch62_371
  · exact degreeUnionBranch62_372
  · exact degreeUnionBranch62_373
  · exact degreeUnionBranch62_374

lemma degreeUnionBranch62_360 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 37 12 degreeUnionState62_360 [12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 37 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_361
  · exact degreeUnionBranch62_362
  · exact degreeUnionBranch62_363
  · exact degreeUnionBranch62_364
  · exact degreeUnionBranch62_369
  · exact degreeUnionBranch62_375
  · exact degreeUnionBranch62_376
  · exact degreeUnionBranch62_377
  · exact degreeUnionBranch62_378

lemma degreeUnionBranch62_383 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 7 degreeUnionState62_383 [7,13,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_384
  · exact degreeUnionBranch62_385
  · exact degreeUnionBranch62_386
  · exact degreeUnionBranch62_387

lemma degreeUnionBranch62_379 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 13 degreeUnionState62_379 [13,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 36 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_380
  · exact degreeUnionBranch62_381
  · exact degreeUnionBranch62_382
  · exact degreeUnionBranch62_383
  · exact degreeUnionBranch62_388
  · exact degreeUnionBranch62_389
  · exact degreeUnionBranch62_390
  · exact degreeUnionBranch62_391
  · exact degreeUnionBranch62_392
  · exact degreeUnionBranch62_393

lemma degreeUnionBranch62_259 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 49 13 degreeUnionState62_259 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 13 at hb
  change 49 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_260
  · exact degreeUnionBranch62_261
  · exact degreeUnionBranch62_262
  · exact degreeUnionBranch62_270
  · exact degreeUnionBranch62_284
  · exact degreeUnionBranch62_306
  · exact degreeUnionBranch62_336
  · exact degreeUnionBranch62_360
  · exact degreeUnionBranch62_379

lemma degreeUnionBranch62_400 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 34 7 degreeUnionState62_400 [7,7,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 34 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_401
  · exact degreeUnionBranch62_402
  · exact degreeUnionBranch62_403
  · exact degreeUnionBranch62_404

lemma degreeUnionBranch62_397 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 41 7 degreeUnionState62_397 [7,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 7 at hb
  change 41 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_398
  · exact degreeUnionBranch62_399
  · exact degreeUnionBranch62_400

lemma degreeUnionBranch62_409 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 33 7 degreeUnionState62_409 [7,8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 33 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_410
  · exact degreeUnionBranch62_411
  · exact degreeUnionBranch62_412
  · exact degreeUnionBranch62_413

lemma degreeUnionBranch62_414 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 8 degreeUnionState62_414 [8,8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_415
  · exact degreeUnionBranch62_416
  · exact degreeUnionBranch62_417
  · exact degreeUnionBranch62_418
  · exact degreeUnionBranch62_419

lemma degreeUnionBranch62_405 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 40 8 degreeUnionState62_405 [8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 8 at hb
  change 40 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_406
  · exact degreeUnionBranch62_407
  · exact degreeUnionBranch62_408
  · exact degreeUnionBranch62_409
  · exact degreeUnionBranch62_414

lemma degreeUnionBranch62_424 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 32 7 degreeUnionState62_424 [7,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_425
  · exact degreeUnionBranch62_426
  · exact degreeUnionBranch62_427
  · exact degreeUnionBranch62_428

lemma degreeUnionBranch62_429 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 8 degreeUnionState62_429 [8,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_430
  · exact degreeUnionBranch62_431
  · exact degreeUnionBranch62_432
  · exact degreeUnionBranch62_433
  · exact degreeUnionBranch62_434

lemma degreeUnionBranch62_435 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 9 degreeUnionState62_435 [9,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_436
  · exact degreeUnionBranch62_437
  · exact degreeUnionBranch62_438
  · exact degreeUnionBranch62_439
  · exact degreeUnionBranch62_440
  · exact degreeUnionBranch62_441

lemma degreeUnionBranch62_420 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 39 9 degreeUnionState62_420 [9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 39 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_421
  · exact degreeUnionBranch62_422
  · exact degreeUnionBranch62_423
  · exact degreeUnionBranch62_424
  · exact degreeUnionBranch62_429
  · exact degreeUnionBranch62_435

lemma degreeUnionBranch62_446 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 31 7 degreeUnionState62_446 [7,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_447
  · exact degreeUnionBranch62_448
  · exact degreeUnionBranch62_449
  · exact degreeUnionBranch62_450

lemma degreeUnionBranch62_451 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 8 degreeUnionState62_451 [8,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_452
  · exact degreeUnionBranch62_453
  · exact degreeUnionBranch62_454
  · exact degreeUnionBranch62_455
  · exact degreeUnionBranch62_456

lemma degreeUnionBranch62_457 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 9 degreeUnionState62_457 [9,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_458
  · exact degreeUnionBranch62_459
  · exact degreeUnionBranch62_460
  · exact degreeUnionBranch62_461
  · exact degreeUnionBranch62_462
  · exact degreeUnionBranch62_463

lemma degreeUnionBranch62_442 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 38 10 degreeUnionState62_442 [10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 38 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_443
  · exact degreeUnionBranch62_444
  · exact degreeUnionBranch62_445
  · exact degreeUnionBranch62_446
  · exact degreeUnionBranch62_451
  · exact degreeUnionBranch62_457
  · exact degreeUnionBranch62_464

lemma degreeUnionBranch62_469 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 30 7 degreeUnionState62_469 [7,11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_470
  · exact degreeUnionBranch62_471
  · exact degreeUnionBranch62_472
  · exact degreeUnionBranch62_473

lemma degreeUnionBranch62_474 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 8 degreeUnionState62_474 [8,11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_475
  · exact degreeUnionBranch62_476
  · exact degreeUnionBranch62_477
  · exact degreeUnionBranch62_478
  · exact degreeUnionBranch62_479

lemma degreeUnionBranch62_465 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 37 11 degreeUnionState62_465 [11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 37 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_466
  · exact degreeUnionBranch62_467
  · exact degreeUnionBranch62_468
  · exact degreeUnionBranch62_469
  · exact degreeUnionBranch62_474
  · exact degreeUnionBranch62_480
  · exact degreeUnionBranch62_481
  · exact degreeUnionBranch62_482

lemma degreeUnionBranch62_487 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 9 29 7 degreeUnionState62_487 [7,12,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_488
  · exact degreeUnionBranch62_489
  · exact degreeUnionBranch62_490
  · exact degreeUnionBranch62_491

lemma degreeUnionBranch62_483 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 36 12 degreeUnionState62_483 [12,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 36 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_484
  · exact degreeUnionBranch62_485
  · exact degreeUnionBranch62_486
  · exact degreeUnionBranch62_487
  · exact degreeUnionBranch62_492
  · exact degreeUnionBranch62_493
  · exact degreeUnionBranch62_494
  · exact degreeUnionBranch62_495
  · exact degreeUnionBranch62_496

lemma degreeUnionBranch62_394 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 48 14 degreeUnionState62_394 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 48 ≤ 11*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_395
  · exact degreeUnionBranch62_396
  · exact degreeUnionBranch62_397
  · exact degreeUnionBranch62_405
  · exact degreeUnionBranch62_420
  · exact degreeUnionBranch62_442
  · exact degreeUnionBranch62_465
  · exact degreeUnionBranch62_483
  · exact degreeUnionBranch62_497
  · exact degreeUnionBranch62_498

lemma degreeUnionBranch62_62 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 62 28 degreeHalfRegions62 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 5 ≤ a at ha
  change a ≤ 28 at hb
  change 62 ≤ 12*a at hn
  have hlo : 6 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_63
  · exact degreeUnionBranch62_64
  · exact degreeUnionBranch62_65
  · exact degreeUnionBranch62_66
  · exact degreeUnionBranch62_67
  · exact degreeUnionBranch62_87
  · exact degreeUnionBranch62_131
  · exact degreeUnionBranch62_259
  · exact degreeUnionBranch62_394
  · exact degreeUnionBranch62_499
  · exact degreeUnionBranch62_500
  · exact degreeUnionBranch62_501
  · exact degreeUnionBranch62_502
  · exact degreeUnionBranch62_503
  · exact degreeUnionBranch62_504
  · exact degreeUnionBranch62_505
  · exact degreeUnionBranch62_506
  · exact degreeUnionBranch62_507
  · exact degreeUnionBranch62_508
  · exact degreeUnionBranch62_509
  · exact degreeUnionBranch62_510
  · exact degreeUnionBranch62_511
  · exact degreeUnionBranch62_512

lemma degreeUnionBranch62_532 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 10 degreeUnionState62_532 [10,10,10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_533
  · exact degreeUnionBranch62_534
  · exact degreeUnionBranch62_535
  · exact degreeUnionBranch62_536
  · exact degreeUnionBranch62_537
  · exact degreeUnionBranch62_538
  · exact degreeUnionBranch62_539

lemma degreeUnionBranch62_525 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 42 10 degreeUnionState62_525 [10,10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 42 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_526
  · exact degreeUnionBranch62_527
  · exact degreeUnionBranch62_528
  · exact degreeUnionBranch62_529
  · exact degreeUnionBranch62_530
  · exact degreeUnionBranch62_531
  · exact degreeUnionBranch62_532

lemma degreeUnionBranch62_519 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 52 10 degreeUnionState62_519 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 52 ≤ 12*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_520
  · exact degreeUnionBranch62_521
  · exact degreeUnionBranch62_522
  · exact degreeUnionBranch62_523
  · exact degreeUnionBranch62_524
  · exact degreeUnionBranch62_525

lemma degreeUnionBranch62_553 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 10 degreeUnionState62_553 [10,10,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_554
  · exact degreeUnionBranch62_555
  · exact degreeUnionBranch62_556
  · exact degreeUnionBranch62_557
  · exact degreeUnionBranch62_558
  · exact degreeUnionBranch62_559
  · exact degreeUnionBranch62_560

lemma degreeUnionBranch62_546 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 41 10 degreeUnionState62_546 [10,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 41 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_547
  · exact degreeUnionBranch62_548
  · exact degreeUnionBranch62_549
  · exact degreeUnionBranch62_550
  · exact degreeUnionBranch62_551
  · exact degreeUnionBranch62_552
  · exact degreeUnionBranch62_553

lemma degreeUnionBranch62_568 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 10 degreeUnionState62_568 [10,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_569
  · exact degreeUnionBranch62_570
  · exact degreeUnionBranch62_571
  · exact degreeUnionBranch62_572
  · exact degreeUnionBranch62_573
  · exact degreeUnionBranch62_574
  · exact degreeUnionBranch62_575
  · exact degreeUnionBranch62_576

lemma degreeUnionBranch62_577 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 11 degreeUnionState62_577 [11,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 11 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_578
  · exact degreeUnionBranch62_579
  · exact degreeUnionBranch62_580
  · exact degreeUnionBranch62_581
  · exact degreeUnionBranch62_582
  · exact degreeUnionBranch62_583
  · exact degreeUnionBranch62_584
  · exact degreeUnionBranch62_585
  · exact degreeUnionBranch62_586

lemma degreeUnionBranch62_561 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 40 11 degreeUnionState62_561 [11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 40 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_562
  · exact degreeUnionBranch62_563
  · exact degreeUnionBranch62_564
  · exact degreeUnionBranch62_565
  · exact degreeUnionBranch62_566
  · exact degreeUnionBranch62_567
  · exact degreeUnionBranch62_568
  · exact degreeUnionBranch62_577

lemma degreeUnionBranch62_540 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 51 11 degreeUnionState62_540 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 11 at hb
  change 51 ≤ 12*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_541
  · exact degreeUnionBranch62_542
  · exact degreeUnionBranch62_543
  · exact degreeUnionBranch62_544
  · exact degreeUnionBranch62_545
  · exact degreeUnionBranch62_546
  · exact degreeUnionBranch62_561

lemma degreeUnionBranch62_596 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 34 8 degreeUnionState62_596 [8,8,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 34 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_597
  · exact degreeUnionBranch62_598
  · exact degreeUnionBranch62_599
  · exact degreeUnionBranch62_600
  · exact degreeUnionBranch62_601

lemma degreeUnionBranch62_591 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 42 8 degreeUnionState62_591 [8,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 42 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_592
  · exact degreeUnionBranch62_593
  · exact degreeUnionBranch62_594
  · exact degreeUnionBranch62_595
  · exact degreeUnionBranch62_596

lemma degreeUnionBranch62_607 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 33 8 degreeUnionState62_607 [8,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 33 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_608
  · exact degreeUnionBranch62_609
  · exact degreeUnionBranch62_610
  · exact degreeUnionBranch62_611
  · exact degreeUnionBranch62_612

lemma degreeUnionBranch62_613 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 9 degreeUnionState62_613 [9,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_614
  · exact degreeUnionBranch62_615
  · exact degreeUnionBranch62_616
  · exact degreeUnionBranch62_617
  · exact degreeUnionBranch62_618
  · exact degreeUnionBranch62_619

lemma degreeUnionBranch62_602 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 41 9 degreeUnionState62_602 [9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 41 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_603
  · exact degreeUnionBranch62_604
  · exact degreeUnionBranch62_605
  · exact degreeUnionBranch62_606
  · exact degreeUnionBranch62_607
  · exact degreeUnionBranch62_613

lemma degreeUnionBranch62_625 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 8 degreeUnionState62_625 [8,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_626
  · exact degreeUnionBranch62_627
  · exact degreeUnionBranch62_628
  · exact degreeUnionBranch62_629
  · exact degreeUnionBranch62_630

lemma degreeUnionBranch62_631 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 9 degreeUnionState62_631 [9,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_632
  · exact degreeUnionBranch62_633
  · exact degreeUnionBranch62_634
  · exact degreeUnionBranch62_635
  · exact degreeUnionBranch62_636
  · exact degreeUnionBranch62_637

lemma degreeUnionBranch62_638 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 10 degreeUnionState62_638 [10,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_639
  · exact degreeUnionBranch62_640
  · exact degreeUnionBranch62_641
  · exact degreeUnionBranch62_642
  · exact degreeUnionBranch62_643
  · exact degreeUnionBranch62_644
  · exact degreeUnionBranch62_645
  · exact degreeUnionBranch62_646

lemma degreeUnionBranch62_620 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 40 10 degreeUnionState62_620 [10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 40 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_621
  · exact degreeUnionBranch62_622
  · exact degreeUnionBranch62_623
  · exact degreeUnionBranch62_624
  · exact degreeUnionBranch62_625
  · exact degreeUnionBranch62_631
  · exact degreeUnionBranch62_638

lemma degreeUnionBranch62_651 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 7 degreeUnionState62_651 [7,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_652
  · exact degreeUnionBranch62_653
  · exact degreeUnionBranch62_654
  · exact degreeUnionBranch62_655

lemma degreeUnionBranch62_656 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 8 degreeUnionState62_656 [8,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_657
  · exact degreeUnionBranch62_658
  · exact degreeUnionBranch62_659
  · exact degreeUnionBranch62_660
  · exact degreeUnionBranch62_661

lemma degreeUnionBranch62_662 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 9 degreeUnionState62_662 [9,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_663
  · exact degreeUnionBranch62_664
  · exact degreeUnionBranch62_665
  · exact degreeUnionBranch62_666
  · exact degreeUnionBranch62_667
  · exact degreeUnionBranch62_668
  · exact degreeUnionBranch62_669

lemma degreeUnionBranch62_670 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 10 degreeUnionState62_670 [10,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_671
  · exact degreeUnionBranch62_672
  · exact degreeUnionBranch62_673
  · exact degreeUnionBranch62_674
  · exact degreeUnionBranch62_675
  · exact degreeUnionBranch62_676
  · exact degreeUnionBranch62_677
  · exact degreeUnionBranch62_678

lemma degreeUnionBranch62_647 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 39 11 degreeUnionState62_647 [11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 39 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_648
  · exact degreeUnionBranch62_649
  · exact degreeUnionBranch62_650
  · exact degreeUnionBranch62_651
  · exact degreeUnionBranch62_656
  · exact degreeUnionBranch62_662
  · exact degreeUnionBranch62_670
  · exact degreeUnionBranch62_679

lemma degreeUnionBranch62_684 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 7 degreeUnionState62_684 [7,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_685
  · exact degreeUnionBranch62_686
  · exact degreeUnionBranch62_687
  · exact degreeUnionBranch62_688

lemma degreeUnionBranch62_689 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 8 degreeUnionState62_689 [8,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_690
  · exact degreeUnionBranch62_691
  · exact degreeUnionBranch62_692
  · exact degreeUnionBranch62_693
  · exact degreeUnionBranch62_694
  · exact degreeUnionBranch62_695

lemma degreeUnionBranch62_696 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 9 degreeUnionState62_696 [9,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_697
  · exact degreeUnionBranch62_698
  · exact degreeUnionBranch62_699
  · exact degreeUnionBranch62_700
  · exact degreeUnionBranch62_701
  · exact degreeUnionBranch62_702
  · exact degreeUnionBranch62_703

lemma degreeUnionBranch62_680 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 38 12 degreeUnionState62_680 [12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 38 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_681
  · exact degreeUnionBranch62_682
  · exact degreeUnionBranch62_683
  · exact degreeUnionBranch62_684
  · exact degreeUnionBranch62_689
  · exact degreeUnionBranch62_696
  · exact degreeUnionBranch62_704
  · exact degreeUnionBranch62_705
  · exact degreeUnionBranch62_706

lemma degreeUnionBranch62_587 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 50 12 degreeUnionState62_587 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 12 at hb
  change 50 ≤ 12*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_588
  · exact degreeUnionBranch62_589
  · exact degreeUnionBranch62_590
  · exact degreeUnionBranch62_591
  · exact degreeUnionBranch62_602
  · exact degreeUnionBranch62_620
  · exact degreeUnionBranch62_647
  · exact degreeUnionBranch62_680

lemma degreeUnionBranch62_710 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 42 7 degreeUnionState62_710 [7,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 42 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_711
  · exact degreeUnionBranch62_712
  · exact degreeUnionBranch62_713
  · exact degreeUnionBranch62_714

lemma degreeUnionBranch62_720 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 33 8 degreeUnionState62_720 [8,8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 33 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_721
  · exact degreeUnionBranch62_722
  · exact degreeUnionBranch62_723
  · exact degreeUnionBranch62_724
  · exact degreeUnionBranch62_725

lemma degreeUnionBranch62_715 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 41 8 degreeUnionState62_715 [8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 41 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_716
  · exact degreeUnionBranch62_717
  · exact degreeUnionBranch62_718
  · exact degreeUnionBranch62_719
  · exact degreeUnionBranch62_720

lemma degreeUnionBranch62_731 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 8 degreeUnionState62_731 [8,9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_732
  · exact degreeUnionBranch62_733
  · exact degreeUnionBranch62_734
  · exact degreeUnionBranch62_735
  · exact degreeUnionBranch62_736

lemma degreeUnionBranch62_737 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 9 degreeUnionState62_737 [9,9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_738
  · exact degreeUnionBranch62_739
  · exact degreeUnionBranch62_740
  · exact degreeUnionBranch62_741
  · exact degreeUnionBranch62_742
  · exact degreeUnionBranch62_743

lemma degreeUnionBranch62_726 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 40 9 degreeUnionState62_726 [9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 40 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_727
  · exact degreeUnionBranch62_728
  · exact degreeUnionBranch62_729
  · exact degreeUnionBranch62_730
  · exact degreeUnionBranch62_731
  · exact degreeUnionBranch62_737

lemma degreeUnionBranch62_748 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 7 degreeUnionState62_748 [7,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_749
  · exact degreeUnionBranch62_750
  · exact degreeUnionBranch62_751
  · exact degreeUnionBranch62_752

lemma degreeUnionBranch62_753 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 8 degreeUnionState62_753 [8,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_754
  · exact degreeUnionBranch62_755
  · exact degreeUnionBranch62_756
  · exact degreeUnionBranch62_757
  · exact degreeUnionBranch62_758

lemma degreeUnionBranch62_759 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 9 degreeUnionState62_759 [9,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_760
  · exact degreeUnionBranch62_761
  · exact degreeUnionBranch62_762
  · exact degreeUnionBranch62_763
  · exact degreeUnionBranch62_764
  · exact degreeUnionBranch62_765
  · exact degreeUnionBranch62_766

lemma degreeUnionBranch62_767 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 10 degreeUnionState62_767 [10,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_768
  · exact degreeUnionBranch62_769
  · exact degreeUnionBranch62_770
  · exact degreeUnionBranch62_771
  · exact degreeUnionBranch62_772
  · exact degreeUnionBranch62_773
  · exact degreeUnionBranch62_774
  · exact degreeUnionBranch62_775

lemma degreeUnionBranch62_744 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 39 10 degreeUnionState62_744 [10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 39 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_745
  · exact degreeUnionBranch62_746
  · exact degreeUnionBranch62_747
  · exact degreeUnionBranch62_748
  · exact degreeUnionBranch62_753
  · exact degreeUnionBranch62_759
  · exact degreeUnionBranch62_767

lemma degreeUnionBranch62_780 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 7 degreeUnionState62_780 [7,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_781
  · exact degreeUnionBranch62_782
  · exact degreeUnionBranch62_783
  · exact degreeUnionBranch62_784

lemma degreeUnionBranch62_785 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 8 degreeUnionState62_785 [8,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_786
  · exact degreeUnionBranch62_787
  · exact degreeUnionBranch62_788
  · exact degreeUnionBranch62_789
  · exact degreeUnionBranch62_790
  · exact degreeUnionBranch62_791

lemma degreeUnionBranch62_792 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 9 degreeUnionState62_792 [9,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_793
  · exact degreeUnionBranch62_794
  · exact degreeUnionBranch62_795
  · exact degreeUnionBranch62_796
  · exact degreeUnionBranch62_797
  · exact degreeUnionBranch62_798
  · exact degreeUnionBranch62_799

lemma degreeUnionBranch62_776 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 38 11 degreeUnionState62_776 [11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 38 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_777
  · exact degreeUnionBranch62_778
  · exact degreeUnionBranch62_779
  · exact degreeUnionBranch62_780
  · exact degreeUnionBranch62_785
  · exact degreeUnionBranch62_792
  · exact degreeUnionBranch62_800
  · exact degreeUnionBranch62_801

lemma degreeUnionBranch62_806 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 7 degreeUnionState62_806 [7,12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_807
  · exact degreeUnionBranch62_808
  · exact degreeUnionBranch62_809
  · exact degreeUnionBranch62_810
  · exact degreeUnionBranch62_811

lemma degreeUnionBranch62_812 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 8 degreeUnionState62_812 [8,12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_813
  · exact degreeUnionBranch62_814
  · exact degreeUnionBranch62_815
  · exact degreeUnionBranch62_816
  · exact degreeUnionBranch62_817
  · exact degreeUnionBranch62_818

lemma degreeUnionBranch62_802 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 37 12 degreeUnionState62_802 [12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 37 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_803
  · exact degreeUnionBranch62_804
  · exact degreeUnionBranch62_805
  · exact degreeUnionBranch62_806
  · exact degreeUnionBranch62_812
  · exact degreeUnionBranch62_819
  · exact degreeUnionBranch62_820
  · exact degreeUnionBranch62_821
  · exact degreeUnionBranch62_822

lemma degreeUnionBranch62_823 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 36 13 degreeUnionState62_823 [13,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 36 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_824
  · exact degreeUnionBranch62_825
  · exact degreeUnionBranch62_826
  · exact degreeUnionBranch62_827
  · exact degreeUnionBranch62_828
  · exact degreeUnionBranch62_829
  · exact degreeUnionBranch62_830
  · exact degreeUnionBranch62_831
  · exact degreeUnionBranch62_832
  · exact degreeUnionBranch62_833

lemma degreeUnionBranch62_707 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 49 13 degreeUnionState62_707 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 13 at hb
  change 49 ≤ 12*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_708
  · exact degreeUnionBranch62_709
  · exact degreeUnionBranch62_710
  · exact degreeUnionBranch62_715
  · exact degreeUnionBranch62_726
  · exact degreeUnionBranch62_744
  · exact degreeUnionBranch62_776
  · exact degreeUnionBranch62_802
  · exact degreeUnionBranch62_823

lemma degreeUnionBranch62_838 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 41 7 degreeUnionState62_838 [7,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 41 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_839
  · exact degreeUnionBranch62_840
  · exact degreeUnionBranch62_841
  · exact degreeUnionBranch62_842

lemma degreeUnionBranch62_848 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 8 degreeUnionState62_848 [8,8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_849
  · exact degreeUnionBranch62_850
  · exact degreeUnionBranch62_851
  · exact degreeUnionBranch62_852
  · exact degreeUnionBranch62_853

lemma degreeUnionBranch62_843 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 40 8 degreeUnionState62_843 [8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 40 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_844
  · exact degreeUnionBranch62_845
  · exact degreeUnionBranch62_846
  · exact degreeUnionBranch62_847
  · exact degreeUnionBranch62_848

lemma degreeUnionBranch62_858 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 32 7 degreeUnionState62_858 [7,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_859
  · exact degreeUnionBranch62_860
  · exact degreeUnionBranch62_861
  · exact degreeUnionBranch62_862

lemma degreeUnionBranch62_863 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 8 degreeUnionState62_863 [8,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_864
  · exact degreeUnionBranch62_865
  · exact degreeUnionBranch62_866
  · exact degreeUnionBranch62_867
  · exact degreeUnionBranch62_868

lemma degreeUnionBranch62_869 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 9 degreeUnionState62_869 [9,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_870
  · exact degreeUnionBranch62_871
  · exact degreeUnionBranch62_872
  · exact degreeUnionBranch62_873
  · exact degreeUnionBranch62_874
  · exact degreeUnionBranch62_875
  · exact degreeUnionBranch62_876

lemma degreeUnionBranch62_854 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 39 9 degreeUnionState62_854 [9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 39 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_855
  · exact degreeUnionBranch62_856
  · exact degreeUnionBranch62_857
  · exact degreeUnionBranch62_858
  · exact degreeUnionBranch62_863
  · exact degreeUnionBranch62_869

lemma degreeUnionBranch62_881 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 31 7 degreeUnionState62_881 [7,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_882
  · exact degreeUnionBranch62_883
  · exact degreeUnionBranch62_884
  · exact degreeUnionBranch62_885

lemma degreeUnionBranch62_886 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 8 degreeUnionState62_886 [8,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_887
  · exact degreeUnionBranch62_888
  · exact degreeUnionBranch62_889
  · exact degreeUnionBranch62_890
  · exact degreeUnionBranch62_891
  · exact degreeUnionBranch62_892

lemma degreeUnionBranch62_893 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 9 degreeUnionState62_893 [9,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_894
  · exact degreeUnionBranch62_895
  · exact degreeUnionBranch62_896
  · exact degreeUnionBranch62_897
  · exact degreeUnionBranch62_898
  · exact degreeUnionBranch62_899
  · exact degreeUnionBranch62_900

lemma degreeUnionBranch62_877 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 38 10 degreeUnionState62_877 [10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 38 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_878
  · exact degreeUnionBranch62_879
  · exact degreeUnionBranch62_880
  · exact degreeUnionBranch62_881
  · exact degreeUnionBranch62_886
  · exact degreeUnionBranch62_893
  · exact degreeUnionBranch62_901

lemma degreeUnionBranch62_906 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 30 7 degreeUnionState62_906 [7,11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 7 at hb
  change 30 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_907
  · exact degreeUnionBranch62_908
  · exact degreeUnionBranch62_909
  · exact degreeUnionBranch62_910
  · exact degreeUnionBranch62_911

lemma degreeUnionBranch62_912 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 10 29 8 degreeUnionState62_912 [8,11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 10*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_913
  · exact degreeUnionBranch62_914
  · exact degreeUnionBranch62_915
  · exact degreeUnionBranch62_916
  · exact degreeUnionBranch62_917
  · exact degreeUnionBranch62_918

lemma degreeUnionBranch62_902 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 37 11 degreeUnionState62_902 [11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 37 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_903
  · exact degreeUnionBranch62_904
  · exact degreeUnionBranch62_905
  · exact degreeUnionBranch62_906
  · exact degreeUnionBranch62_912
  · exact degreeUnionBranch62_919
  · exact degreeUnionBranch62_920
  · exact degreeUnionBranch62_921

lemma degreeUnionBranch62_922 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 36 12 degreeUnionState62_922 [12,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 36 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_923
  · exact degreeUnionBranch62_924
  · exact degreeUnionBranch62_925
  · exact degreeUnionBranch62_926
  · exact degreeUnionBranch62_927
  · exact degreeUnionBranch62_928
  · exact degreeUnionBranch62_929
  · exact degreeUnionBranch62_930
  · exact degreeUnionBranch62_931

lemma degreeUnionBranch62_834 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 48 14 degreeUnionState62_834 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 48 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_835
  · exact degreeUnionBranch62_836
  · exact degreeUnionBranch62_837
  · exact degreeUnionBranch62_838
  · exact degreeUnionBranch62_843
  · exact degreeUnionBranch62_854
  · exact degreeUnionBranch62_877
  · exact degreeUnionBranch62_902
  · exact degreeUnionBranch62_922
  · exact degreeUnionBranch62_932
  · exact degreeUnionBranch62_933

lemma degreeUnionBranch62_513 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 62 28 degreeHalfRegions62 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 28 at hb
  change 62 ≤ 13*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_514
  · exact degreeUnionBranch62_515
  · exact degreeUnionBranch62_516
  · exact degreeUnionBranch62_517
  · exact degreeUnionBranch62_518
  · exact degreeUnionBranch62_519
  · exact degreeUnionBranch62_540
  · exact degreeUnionBranch62_587
  · exact degreeUnionBranch62_707
  · exact degreeUnionBranch62_834
  · exact degreeUnionBranch62_934
  · exact degreeUnionBranch62_935
  · exact degreeUnionBranch62_936
  · exact degreeUnionBranch62_937
  · exact degreeUnionBranch62_938
  · exact degreeUnionBranch62_939
  · exact degreeUnionBranch62_940
  · exact degreeUnionBranch62_941
  · exact degreeUnionBranch62_942
  · exact degreeUnionBranch62_943
  · exact degreeUnionBranch62_944
  · exact degreeUnionBranch62_945
  · exact degreeUnionBranch62_946
  · exact degreeUnionBranch62_947

lemma degreeUnionBranch62_954 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 52 10 degreeUnionState62_954 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 52 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_955
  · exact degreeUnionBranch62_956
  · exact degreeUnionBranch62_957
  · exact degreeUnionBranch62_958
  · exact degreeUnionBranch62_959
  · exact degreeUnionBranch62_960
  · exact degreeUnionBranch62_961

lemma degreeUnionBranch62_969 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 41 10 degreeUnionState62_969 [10,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 41 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_970
  · exact degreeUnionBranch62_971
  · exact degreeUnionBranch62_972
  · exact degreeUnionBranch62_973
  · exact degreeUnionBranch62_974
  · exact degreeUnionBranch62_975
  · exact degreeUnionBranch62_976

lemma degreeUnionBranch62_984 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 10 degreeUnionState62_984 [10,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_985
  · exact degreeUnionBranch62_986
  · exact degreeUnionBranch62_987
  · exact degreeUnionBranch62_988
  · exact degreeUnionBranch62_989
  · exact degreeUnionBranch62_990
  · exact degreeUnionBranch62_991
  · exact degreeUnionBranch62_992

lemma degreeUnionBranch62_993 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 11 degreeUnionState62_993 [11,11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 11 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_994
  · exact degreeUnionBranch62_995
  · exact degreeUnionBranch62_996
  · exact degreeUnionBranch62_997
  · exact degreeUnionBranch62_998
  · exact degreeUnionBranch62_999
  · exact degreeUnionBranch62_1000
  · exact degreeUnionBranch62_1001
  · exact degreeUnionBranch62_1002

lemma degreeUnionBranch62_977 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 40 11 degreeUnionState62_977 [11,11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 40 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_978
  · exact degreeUnionBranch62_979
  · exact degreeUnionBranch62_980
  · exact degreeUnionBranch62_981
  · exact degreeUnionBranch62_982
  · exact degreeUnionBranch62_983
  · exact degreeUnionBranch62_984
  · exact degreeUnionBranch62_993

lemma degreeUnionBranch62_962 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 51 11 degreeUnionState62_962 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 51 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_963
  · exact degreeUnionBranch62_964
  · exact degreeUnionBranch62_965
  · exact degreeUnionBranch62_966
  · exact degreeUnionBranch62_967
  · exact degreeUnionBranch62_968
  · exact degreeUnionBranch62_969
  · exact degreeUnionBranch62_977

lemma degreeUnionBranch62_1013 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 34 8 degreeUnionState62_1013 [8,8,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 34 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1014
  · exact degreeUnionBranch62_1015
  · exact degreeUnionBranch62_1016
  · exact degreeUnionBranch62_1017
  · exact degreeUnionBranch62_1018

lemma degreeUnionBranch62_1008 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 42 8 degreeUnionState62_1008 [8,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 42 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1009
  · exact degreeUnionBranch62_1010
  · exact degreeUnionBranch62_1011
  · exact degreeUnionBranch62_1012
  · exact degreeUnionBranch62_1013

lemma degreeUnionBranch62_1024 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 8 degreeUnionState62_1024 [8,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 33 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1025
  · exact degreeUnionBranch62_1026
  · exact degreeUnionBranch62_1027
  · exact degreeUnionBranch62_1028
  · exact degreeUnionBranch62_1029
  · exact degreeUnionBranch62_1030

lemma degreeUnionBranch62_1031 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 9 degreeUnionState62_1031 [9,9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 32 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1032
  · exact degreeUnionBranch62_1033
  · exact degreeUnionBranch62_1034
  · exact degreeUnionBranch62_1035
  · exact degreeUnionBranch62_1036
  · exact degreeUnionBranch62_1037
  · exact degreeUnionBranch62_1038

lemma degreeUnionBranch62_1019 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 41 9 degreeUnionState62_1019 [9,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 41 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1020
  · exact degreeUnionBranch62_1021
  · exact degreeUnionBranch62_1022
  · exact degreeUnionBranch62_1023
  · exact degreeUnionBranch62_1024
  · exact degreeUnionBranch62_1031

lemma degreeUnionBranch62_1044 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 8 degreeUnionState62_1044 [8,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1045
  · exact degreeUnionBranch62_1046
  · exact degreeUnionBranch62_1047
  · exact degreeUnionBranch62_1048
  · exact degreeUnionBranch62_1049
  · exact degreeUnionBranch62_1050

lemma degreeUnionBranch62_1051 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 9 degreeUnionState62_1051 [9,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 31 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1052
  · exact degreeUnionBranch62_1053
  · exact degreeUnionBranch62_1054
  · exact degreeUnionBranch62_1055
  · exact degreeUnionBranch62_1056
  · exact degreeUnionBranch62_1057
  · exact degreeUnionBranch62_1058

lemma degreeUnionBranch62_1059 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 10 degreeUnionState62_1059 [10,10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1060
  · exact degreeUnionBranch62_1061
  · exact degreeUnionBranch62_1062
  · exact degreeUnionBranch62_1063
  · exact degreeUnionBranch62_1064
  · exact degreeUnionBranch62_1065
  · exact degreeUnionBranch62_1066
  · exact degreeUnionBranch62_1067

lemma degreeUnionBranch62_1039 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 40 10 degreeUnionState62_1039 [10,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 40 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1040
  · exact degreeUnionBranch62_1041
  · exact degreeUnionBranch62_1042
  · exact degreeUnionBranch62_1043
  · exact degreeUnionBranch62_1044
  · exact degreeUnionBranch62_1051
  · exact degreeUnionBranch62_1059

lemma degreeUnionBranch62_1073 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 8 degreeUnionState62_1073 [8,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1074
  · exact degreeUnionBranch62_1075
  · exact degreeUnionBranch62_1076
  · exact degreeUnionBranch62_1077
  · exact degreeUnionBranch62_1078
  · exact degreeUnionBranch62_1079

lemma degreeUnionBranch62_1080 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 9 degreeUnionState62_1080 [9,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1081
  · exact degreeUnionBranch62_1082
  · exact degreeUnionBranch62_1083
  · exact degreeUnionBranch62_1084
  · exact degreeUnionBranch62_1085
  · exact degreeUnionBranch62_1086
  · exact degreeUnionBranch62_1087

lemma degreeUnionBranch62_1088 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 10 degreeUnionState62_1088 [10,11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1089
  · exact degreeUnionBranch62_1090
  · exact degreeUnionBranch62_1091
  · exact degreeUnionBranch62_1092
  · exact degreeUnionBranch62_1093
  · exact degreeUnionBranch62_1094
  · exact degreeUnionBranch62_1095
  · exact degreeUnionBranch62_1096

lemma degreeUnionBranch62_1068 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 39 11 degreeUnionState62_1068 [11,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 39 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1069
  · exact degreeUnionBranch62_1070
  · exact degreeUnionBranch62_1071
  · exact degreeUnionBranch62_1072
  · exact degreeUnionBranch62_1073
  · exact degreeUnionBranch62_1080
  · exact degreeUnionBranch62_1088
  · exact degreeUnionBranch62_1097

lemma degreeUnionBranch62_1103 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 8 degreeUnionState62_1103 [8,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1104
  · exact degreeUnionBranch62_1105
  · exact degreeUnionBranch62_1106
  · exact degreeUnionBranch62_1107
  · exact degreeUnionBranch62_1108
  · exact degreeUnionBranch62_1109

lemma degreeUnionBranch62_1110 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 9 degreeUnionState62_1110 [9,12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1111
  · exact degreeUnionBranch62_1112
  · exact degreeUnionBranch62_1113
  · exact degreeUnionBranch62_1114
  · exact degreeUnionBranch62_1115
  · exact degreeUnionBranch62_1116
  · exact degreeUnionBranch62_1117

lemma degreeUnionBranch62_1098 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 38 12 degreeUnionState62_1098 [12,12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 38 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1099
  · exact degreeUnionBranch62_1100
  · exact degreeUnionBranch62_1101
  · exact degreeUnionBranch62_1102
  · exact degreeUnionBranch62_1103
  · exact degreeUnionBranch62_1110
  · exact degreeUnionBranch62_1118
  · exact degreeUnionBranch62_1119
  · exact degreeUnionBranch62_1120

lemma degreeUnionBranch62_1003 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 50 12 degreeUnionState62_1003 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 50 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1004
  · exact degreeUnionBranch62_1005
  · exact degreeUnionBranch62_1006
  · exact degreeUnionBranch62_1007
  · exact degreeUnionBranch62_1008
  · exact degreeUnionBranch62_1019
  · exact degreeUnionBranch62_1039
  · exact degreeUnionBranch62_1068
  · exact degreeUnionBranch62_1098

lemma degreeUnionBranch62_1131 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 33 8 degreeUnionState62_1131 [8,8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 33 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1132
  · exact degreeUnionBranch62_1133
  · exact degreeUnionBranch62_1134
  · exact degreeUnionBranch62_1135
  · exact degreeUnionBranch62_1136
  · exact degreeUnionBranch62_1137

lemma degreeUnionBranch62_1126 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 41 8 degreeUnionState62_1126 [8,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 41 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1127
  · exact degreeUnionBranch62_1128
  · exact degreeUnionBranch62_1129
  · exact degreeUnionBranch62_1130
  · exact degreeUnionBranch62_1131

lemma degreeUnionBranch62_1143 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 8 degreeUnionState62_1143 [8,9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1144
  · exact degreeUnionBranch62_1145
  · exact degreeUnionBranch62_1146
  · exact degreeUnionBranch62_1147
  · exact degreeUnionBranch62_1148
  · exact degreeUnionBranch62_1149

lemma degreeUnionBranch62_1150 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 9 degreeUnionState62_1150 [9,9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 31 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1151
  · exact degreeUnionBranch62_1152
  · exact degreeUnionBranch62_1153
  · exact degreeUnionBranch62_1154
  · exact degreeUnionBranch62_1155
  · exact degreeUnionBranch62_1156
  · exact degreeUnionBranch62_1157

lemma degreeUnionBranch62_1138 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 40 9 degreeUnionState62_1138 [9,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 40 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1139
  · exact degreeUnionBranch62_1140
  · exact degreeUnionBranch62_1141
  · exact degreeUnionBranch62_1142
  · exact degreeUnionBranch62_1143
  · exact degreeUnionBranch62_1150

lemma degreeUnionBranch62_1163 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 8 degreeUnionState62_1163 [8,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1164
  · exact degreeUnionBranch62_1165
  · exact degreeUnionBranch62_1166
  · exact degreeUnionBranch62_1167
  · exact degreeUnionBranch62_1168
  · exact degreeUnionBranch62_1169

lemma degreeUnionBranch62_1170 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 9 degreeUnionState62_1170 [9,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1171
  · exact degreeUnionBranch62_1172
  · exact degreeUnionBranch62_1173
  · exact degreeUnionBranch62_1174
  · exact degreeUnionBranch62_1175
  · exact degreeUnionBranch62_1176
  · exact degreeUnionBranch62_1177

lemma degreeUnionBranch62_1178 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 10 degreeUnionState62_1178 [10,10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1179
  · exact degreeUnionBranch62_1180
  · exact degreeUnionBranch62_1181
  · exact degreeUnionBranch62_1182
  · exact degreeUnionBranch62_1183
  · exact degreeUnionBranch62_1184
  · exact degreeUnionBranch62_1185
  · exact degreeUnionBranch62_1186

lemma degreeUnionBranch62_1158 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 39 10 degreeUnionState62_1158 [10,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 39 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1159
  · exact degreeUnionBranch62_1160
  · exact degreeUnionBranch62_1161
  · exact degreeUnionBranch62_1162
  · exact degreeUnionBranch62_1163
  · exact degreeUnionBranch62_1170
  · exact degreeUnionBranch62_1178

lemma degreeUnionBranch62_1192 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 8 degreeUnionState62_1192 [8,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1193
  · exact degreeUnionBranch62_1194
  · exact degreeUnionBranch62_1195
  · exact degreeUnionBranch62_1196
  · exact degreeUnionBranch62_1197
  · exact degreeUnionBranch62_1198

lemma degreeUnionBranch62_1199 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 9 degreeUnionState62_1199 [9,11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1200
  · exact degreeUnionBranch62_1201
  · exact degreeUnionBranch62_1202
  · exact degreeUnionBranch62_1203
  · exact degreeUnionBranch62_1204
  · exact degreeUnionBranch62_1205
  · exact degreeUnionBranch62_1206

lemma degreeUnionBranch62_1187 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 38 11 degreeUnionState62_1187 [11,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 38 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1188
  · exact degreeUnionBranch62_1189
  · exact degreeUnionBranch62_1190
  · exact degreeUnionBranch62_1191
  · exact degreeUnionBranch62_1192
  · exact degreeUnionBranch62_1199
  · exact degreeUnionBranch62_1207
  · exact degreeUnionBranch62_1208

lemma degreeUnionBranch62_1214 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 8 degreeUnionState62_1214 [8,12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1215
  · exact degreeUnionBranch62_1216
  · exact degreeUnionBranch62_1217
  · exact degreeUnionBranch62_1218
  · exact degreeUnionBranch62_1219
  · exact degreeUnionBranch62_1220

lemma degreeUnionBranch62_1209 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 37 12 degreeUnionState62_1209 [12,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 37 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1210
  · exact degreeUnionBranch62_1211
  · exact degreeUnionBranch62_1212
  · exact degreeUnionBranch62_1213
  · exact degreeUnionBranch62_1214
  · exact degreeUnionBranch62_1221
  · exact degreeUnionBranch62_1222
  · exact degreeUnionBranch62_1223
  · exact degreeUnionBranch62_1224

lemma degreeUnionBranch62_1225 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 36 13 degreeUnionState62_1225 [13,13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 36 ≤ 12*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1226
  · exact degreeUnionBranch62_1227
  · exact degreeUnionBranch62_1228
  · exact degreeUnionBranch62_1229
  · exact degreeUnionBranch62_1230
  · exact degreeUnionBranch62_1231
  · exact degreeUnionBranch62_1232
  · exact degreeUnionBranch62_1233
  · exact degreeUnionBranch62_1234
  · exact degreeUnionBranch62_1235
  · exact degreeUnionBranch62_1236

lemma degreeUnionBranch62_1121 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 49 13 degreeUnionState62_1121 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 49 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1122
  · exact degreeUnionBranch62_1123
  · exact degreeUnionBranch62_1124
  · exact degreeUnionBranch62_1125
  · exact degreeUnionBranch62_1126
  · exact degreeUnionBranch62_1138
  · exact degreeUnionBranch62_1158
  · exact degreeUnionBranch62_1187
  · exact degreeUnionBranch62_1209
  · exact degreeUnionBranch62_1225

lemma degreeUnionBranch62_1247 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 32 8 degreeUnionState62_1247 [8,8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 32 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1248
  · exact degreeUnionBranch62_1249
  · exact degreeUnionBranch62_1250
  · exact degreeUnionBranch62_1251
  · exact degreeUnionBranch62_1252
  · exact degreeUnionBranch62_1253

lemma degreeUnionBranch62_1242 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 40 8 degreeUnionState62_1242 [8,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 40 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1243
  · exact degreeUnionBranch62_1244
  · exact degreeUnionBranch62_1245
  · exact degreeUnionBranch62_1246
  · exact degreeUnionBranch62_1247

lemma degreeUnionBranch62_1259 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 31 8 degreeUnionState62_1259 [8,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1260
  · exact degreeUnionBranch62_1261
  · exact degreeUnionBranch62_1262
  · exact degreeUnionBranch62_1263
  · exact degreeUnionBranch62_1264
  · exact degreeUnionBranch62_1265

lemma degreeUnionBranch62_1266 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 9 degreeUnionState62_1266 [9,9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1267
  · exact degreeUnionBranch62_1268
  · exact degreeUnionBranch62_1269
  · exact degreeUnionBranch62_1270
  · exact degreeUnionBranch62_1271
  · exact degreeUnionBranch62_1272
  · exact degreeUnionBranch62_1273

lemma degreeUnionBranch62_1254 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 39 9 degreeUnionState62_1254 [9,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 39 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1255
  · exact degreeUnionBranch62_1256
  · exact degreeUnionBranch62_1257
  · exact degreeUnionBranch62_1258
  · exact degreeUnionBranch62_1259
  · exact degreeUnionBranch62_1266

lemma degreeUnionBranch62_1279 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 30 8 degreeUnionState62_1279 [8,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 30 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1280
  · exact degreeUnionBranch62_1281
  · exact degreeUnionBranch62_1282
  · exact degreeUnionBranch62_1283
  · exact degreeUnionBranch62_1284
  · exact degreeUnionBranch62_1285

lemma degreeUnionBranch62_1286 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 9 degreeUnionState62_1286 [9,10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 9 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1287
  · exact degreeUnionBranch62_1288
  · exact degreeUnionBranch62_1289
  · exact degreeUnionBranch62_1290
  · exact degreeUnionBranch62_1291
  · exact degreeUnionBranch62_1292
  · exact degreeUnionBranch62_1293

lemma degreeUnionBranch62_1274 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 38 10 degreeUnionState62_1274 [10,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 38 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1275
  · exact degreeUnionBranch62_1276
  · exact degreeUnionBranch62_1277
  · exact degreeUnionBranch62_1278
  · exact degreeUnionBranch62_1279
  · exact degreeUnionBranch62_1286
  · exact degreeUnionBranch62_1294

lemma degreeUnionBranch62_1300 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 11 29 8 degreeUnionState62_1300 [8,11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 8 at hb
  change 29 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1301
  · exact degreeUnionBranch62_1302
  · exact degreeUnionBranch62_1303
  · exact degreeUnionBranch62_1304
  · exact degreeUnionBranch62_1305
  · exact degreeUnionBranch62_1306

lemma degreeUnionBranch62_1295 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 37 11 degreeUnionState62_1295 [11,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 37 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1296
  · exact degreeUnionBranch62_1297
  · exact degreeUnionBranch62_1298
  · exact degreeUnionBranch62_1299
  · exact degreeUnionBranch62_1300
  · exact degreeUnionBranch62_1307
  · exact degreeUnionBranch62_1308
  · exact degreeUnionBranch62_1309

lemma degreeUnionBranch62_1310 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 12 36 12 degreeUnionState62_1310 [12,14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 36 ≤ 12*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1311
  · exact degreeUnionBranch62_1312
  · exact degreeUnionBranch62_1313
  · exact degreeUnionBranch62_1314
  · exact degreeUnionBranch62_1315
  · exact degreeUnionBranch62_1316
  · exact degreeUnionBranch62_1317
  · exact degreeUnionBranch62_1318
  · exact degreeUnionBranch62_1319
  · exact degreeUnionBranch62_1320

lemma degreeUnionBranch62_1237 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 13 48 14 degreeUnionState62_1237 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 48 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_1238
  · exact degreeUnionBranch62_1239
  · exact degreeUnionBranch62_1240
  · exact degreeUnionBranch62_1241
  · exact degreeUnionBranch62_1242
  · exact degreeUnionBranch62_1254
  · exact degreeUnionBranch62_1274
  · exact degreeUnionBranch62_1295
  · exact degreeUnionBranch62_1310
  · exact degreeUnionBranch62_1321
  · exact degreeUnionBranch62_1322

lemma degreeUnionBranch62_948 : checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) 14 62 28 degreeHalfRegions62 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 28 at hb
  change 62 ≤ 14*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch62_949
  · exact degreeUnionBranch62_950
  · exact degreeUnionBranch62_951
  · exact degreeUnionBranch62_952
  · exact degreeUnionBranch62_953
  · exact degreeUnionBranch62_954
  · exact degreeUnionBranch62_962
  · exact degreeUnionBranch62_1003
  · exact degreeUnionBranch62_1121
  · exact degreeUnionBranch62_1237
  · exact degreeUnionBranch62_1323
  · exact degreeUnionBranch62_1324
  · exact degreeUnionBranch62_1325
  · exact degreeUnionBranch62_1326
  · exact degreeUnionBranch62_1327
  · exact degreeUnionBranch62_1328
  · exact degreeUnionBranch62_1329
  · exact degreeUnionBranch62_1330
  · exact degreeUnionBranch62_1331
  · exact degreeUnionBranch62_1332
  · exact degreeUnionBranch62_1333
  · exact degreeUnionBranch62_1334
  · exact degreeUnionBranch62_1335
  · exact degreeUnionBranch62_1336

lemma degreeUnionCheck62 : ∀ h ≤ 28,
    checkRegionPrefixes (quickResidual 8 13 degreeQs62 degreeTree62) h 62 28 degreeHalfRegions62 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch62_0
  · exact degreeUnionBranch62_1
  · exact degreeUnionBranch62_2
  · exact degreeUnionBranch62_3
  · exact degreeUnionBranch62_4
  · exact degreeUnionBranch62_5
  · exact degreeUnionBranch62_6
  · exact degreeUnionBranch62_7
  · exact degreeUnionBranch62_8
  · exact degreeUnionBranch62_9
  · exact degreeUnionBranch62_10
  · exact degreeUnionBranch62_11
  · exact degreeUnionBranch62_62
  · exact degreeUnionBranch62_513
  · exact degreeUnionBranch62_948
  · exact degreeUnionBranch62_1337
  · exact degreeUnionBranch62_1338
  · exact degreeUnionBranch62_1339
  · exact degreeUnionBranch62_1340
  · exact degreeUnionBranch62_1341
  · exact degreeUnionBranch62_1342
  · exact degreeUnionBranch62_1343
  · exact degreeUnionBranch62_1344
  · exact degreeUnionBranch62_1345
  · exact degreeUnionBranch62_1346
  · exact degreeUnionBranch62_1347
  · exact degreeUnionBranch62_1348
  · exact degreeUnionBranch62_1349
  · exact degreeUnionBranch62_1350

lemma degreeHalfCover62 : ∀ R ∈ degreeRegions62,
    R ∈ degreeHalfRegions62 ∨ (R.2,R.1) ∈ degreeHalfRegions62 := by decide +kernel

lemma degreeDiagramRegionsChecked62 : ∀ R ∈ degreeRegions62,
    ∀ μ : YoungDiagram, μ.card = 62 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP62 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck62 degreeHalfHeight62 degreeHalfWidth62
    degreeHalfCover62

end UniversalTensorSquare
end

end OAI
