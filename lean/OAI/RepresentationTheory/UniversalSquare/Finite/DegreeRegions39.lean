import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Support.SplitUnionRowChecker
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves39

namespace OAI

/-! Degree Regions 39. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch39_12 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 31 8 degreeUnionState39_12 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_13
  · exact degreeUnionBranch39_14
  · exact degreeUnionBranch39_15
  · exact degreeUnionBranch39_16

lemma degreeUnionBranch39_17 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 30 9 degreeUnionState39_17 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_18
  · exact degreeUnionBranch39_19
  · exact degreeUnionBranch39_20
  · exact degreeUnionBranch39_21
  · exact degreeUnionBranch39_22

lemma degreeUnionBranch39_23 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 29 10 degreeUnionState39_23 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_24
  · exact degreeUnionBranch39_25
  · exact degreeUnionBranch39_26
  · exact degreeUnionBranch39_27
  · exact degreeUnionBranch39_28
  · exact degreeUnionBranch39_29

lemma degreeUnionBranch39_30 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 28 11 degreeUnionState39_30 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 11 at hb
  change 28 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_31
  · exact degreeUnionBranch39_32
  · exact degreeUnionBranch39_33
  · exact degreeUnionBranch39_34
  · exact degreeUnionBranch39_35
  · exact degreeUnionBranch39_36
  · exact degreeUnionBranch39_37
  · exact degreeUnionBranch39_38

lemma degreeUnionBranch39_39 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 27 12 degreeUnionState39_39 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 27 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_40
  · exact degreeUnionBranch39_41
  · exact degreeUnionBranch39_42
  · exact degreeUnionBranch39_43
  · exact degreeUnionBranch39_44
  · exact degreeUnionBranch39_45
  · exact degreeUnionBranch39_46
  · exact degreeUnionBranch39_47
  · exact degreeUnionBranch39_48

lemma degreeUnionBranch39_49 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 26 13 degreeUnionState39_49 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 26 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_50
  · exact degreeUnionBranch39_51
  · exact degreeUnionBranch39_52
  · exact degreeUnionBranch39_53
  · exact degreeUnionBranch39_54
  · exact degreeUnionBranch39_55
  · exact degreeUnionBranch39_56
  · exact degreeUnionBranch39_57
  · exact degreeUnionBranch39_58
  · exact degreeUnionBranch39_59

lemma degreeUnionBranch39_60 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 25 14 degreeUnionState39_60 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 25 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_61
  · exact degreeUnionBranch39_62
  · exact degreeUnionBranch39_63
  · exact degreeUnionBranch39_64
  · exact degreeUnionBranch39_65
  · exact degreeUnionBranch39_66
  · exact degreeUnionBranch39_67
  · exact degreeUnionBranch39_68
  · exact degreeUnionBranch39_69
  · exact degreeUnionBranch39_70
  · exact degreeUnionBranch39_71

lemma degreeUnionBranch39_72 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 24 15 degreeUnionState39_72 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 15 at hb
  change 24 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_73
  · exact degreeUnionBranch39_74
  · exact degreeUnionBranch39_75
  · exact degreeUnionBranch39_76
  · exact degreeUnionBranch39_77
  · exact degreeUnionBranch39_78
  · exact degreeUnionBranch39_79
  · exact degreeUnionBranch39_80
  · exact degreeUnionBranch39_81
  · exact degreeUnionBranch39_82
  · exact degreeUnionBranch39_83
  · exact degreeUnionBranch39_84

lemma degreeUnionBranch39_85 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 7 23 16 degreeUnionState39_85 [16] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 16 at hb
  change 23 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_86
  · exact degreeUnionBranch39_87
  · exact degreeUnionBranch39_88
  · exact degreeUnionBranch39_89
  · exact degreeUnionBranch39_90
  · exact degreeUnionBranch39_91
  · exact degreeUnionBranch39_92
  · exact degreeUnionBranch39_93
  · exact degreeUnionBranch39_94
  · exact degreeUnionBranch39_95
  · exact degreeUnionBranch39_96
  · exact degreeUnionBranch39_97
  · exact degreeUnionBranch39_98

lemma degreeUnionBranch39_8 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 39 38 degreeHalfRegions39 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 38 at hb
  change 39 ≤ 8*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_9
  · exact degreeUnionBranch39_10
  · exact degreeUnionBranch39_11
  · exact degreeUnionBranch39_12
  · exact degreeUnionBranch39_17
  · exact degreeUnionBranch39_23
  · exact degreeUnionBranch39_30
  · exact degreeUnionBranch39_39
  · exact degreeUnionBranch39_49
  · exact degreeUnionBranch39_60
  · exact degreeUnionBranch39_72
  · exact degreeUnionBranch39_85
  · exact degreeUnionBranch39_99
  · exact degreeUnionBranch39_100
  · exact degreeUnionBranch39_101
  · exact degreeUnionBranch39_102
  · exact degreeUnionBranch39_103
  · exact degreeUnionBranch39_104
  · exact degreeUnionBranch39_105
  · exact degreeUnionBranch39_106
  · exact degreeUnionBranch39_107
  · exact degreeUnionBranch39_108
  · exact degreeUnionBranch39_109
  · exact degreeUnionBranch39_110
  · exact degreeUnionBranch39_111
  · exact degreeUnionBranch39_112
  · exact degreeUnionBranch39_113
  · exact degreeUnionBranch39_114
  · exact degreeUnionBranch39_115
  · exact degreeUnionBranch39_116
  · exact degreeUnionBranch39_117
  · exact degreeUnionBranch39_118
  · exact degreeUnionBranch39_119
  · exact degreeUnionBranch39_120

lemma degreeUnionBranch39_125 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 31 8 degreeUnionState39_125 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_126
  · exact degreeUnionBranch39_127
  · exact degreeUnionBranch39_128
  · exact degreeUnionBranch39_129
  · exact degreeUnionBranch39_130

lemma degreeUnionBranch39_131 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 30 9 degreeUnionState39_131 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_132
  · exact degreeUnionBranch39_133
  · exact degreeUnionBranch39_134
  · exact degreeUnionBranch39_135
  · exact degreeUnionBranch39_136
  · exact degreeUnionBranch39_137

lemma degreeUnionBranch39_138 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 29 10 degreeUnionState39_138 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_139
  · exact degreeUnionBranch39_140
  · exact degreeUnionBranch39_141
  · exact degreeUnionBranch39_142
  · exact degreeUnionBranch39_143
  · exact degreeUnionBranch39_144
  · exact degreeUnionBranch39_145

lemma degreeUnionBranch39_146 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 28 11 degreeUnionState39_146 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 28 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_147
  · exact degreeUnionBranch39_148
  · exact degreeUnionBranch39_149
  · exact degreeUnionBranch39_150
  · exact degreeUnionBranch39_151
  · exact degreeUnionBranch39_152
  · exact degreeUnionBranch39_153
  · exact degreeUnionBranch39_154

lemma degreeUnionBranch39_155 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 27 12 degreeUnionState39_155 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 27 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_156
  · exact degreeUnionBranch39_157
  · exact degreeUnionBranch39_158
  · exact degreeUnionBranch39_159
  · exact degreeUnionBranch39_160
  · exact degreeUnionBranch39_161
  · exact degreeUnionBranch39_162
  · exact degreeUnionBranch39_163
  · exact degreeUnionBranch39_164

lemma degreeUnionBranch39_165 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 26 13 degreeUnionState39_165 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_166
  · exact degreeUnionBranch39_167
  · exact degreeUnionBranch39_168
  · exact degreeUnionBranch39_169
  · exact degreeUnionBranch39_170
  · exact degreeUnionBranch39_171
  · exact degreeUnionBranch39_172
  · exact degreeUnionBranch39_173
  · exact degreeUnionBranch39_174
  · exact degreeUnionBranch39_175

lemma degreeUnionBranch39_176 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 25 14 degreeUnionState39_176 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 25 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_177
  · exact degreeUnionBranch39_178
  · exact degreeUnionBranch39_179
  · exact degreeUnionBranch39_180
  · exact degreeUnionBranch39_181
  · exact degreeUnionBranch39_182
  · exact degreeUnionBranch39_183
  · exact degreeUnionBranch39_184
  · exact degreeUnionBranch39_185
  · exact degreeUnionBranch39_186
  · exact degreeUnionBranch39_187

lemma degreeUnionBranch39_188 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 8 24 15 degreeUnionState39_188 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 15 at hb
  change 24 ≤ 8*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_189
  · exact degreeUnionBranch39_190
  · exact degreeUnionBranch39_191
  · exact degreeUnionBranch39_192
  · exact degreeUnionBranch39_193
  · exact degreeUnionBranch39_194
  · exact degreeUnionBranch39_195
  · exact degreeUnionBranch39_196
  · exact degreeUnionBranch39_197
  · exact degreeUnionBranch39_198
  · exact degreeUnionBranch39_199
  · exact degreeUnionBranch39_200
  · exact degreeUnionBranch39_201

lemma degreeUnionBranch39_121 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 39 38 degreeHalfRegions39 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 38 at hb
  change 39 ≤ 9*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_122
  · exact degreeUnionBranch39_123
  · exact degreeUnionBranch39_124
  · exact degreeUnionBranch39_125
  · exact degreeUnionBranch39_131
  · exact degreeUnionBranch39_138
  · exact degreeUnionBranch39_146
  · exact degreeUnionBranch39_155
  · exact degreeUnionBranch39_165
  · exact degreeUnionBranch39_176
  · exact degreeUnionBranch39_188
  · exact degreeUnionBranch39_202
  · exact degreeUnionBranch39_203
  · exact degreeUnionBranch39_204
  · exact degreeUnionBranch39_205
  · exact degreeUnionBranch39_206
  · exact degreeUnionBranch39_207
  · exact degreeUnionBranch39_208
  · exact degreeUnionBranch39_209
  · exact degreeUnionBranch39_210
  · exact degreeUnionBranch39_211
  · exact degreeUnionBranch39_212
  · exact degreeUnionBranch39_213
  · exact degreeUnionBranch39_214
  · exact degreeUnionBranch39_215
  · exact degreeUnionBranch39_216
  · exact degreeUnionBranch39_217
  · exact degreeUnionBranch39_218
  · exact degreeUnionBranch39_219
  · exact degreeUnionBranch39_220
  · exact degreeUnionBranch39_221
  · exact degreeUnionBranch39_222
  · exact degreeUnionBranch39_223
  · exact degreeUnionBranch39_224

lemma degreeUnionBranch39_230 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 31 8 degreeUnionState39_230 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_231
  · exact degreeUnionBranch39_232
  · exact degreeUnionBranch39_233
  · exact degreeUnionBranch39_234
  · exact degreeUnionBranch39_235

lemma degreeUnionBranch39_236 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 30 9 degreeUnionState39_236 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_237
  · exact degreeUnionBranch39_238
  · exact degreeUnionBranch39_239
  · exact degreeUnionBranch39_240
  · exact degreeUnionBranch39_241
  · exact degreeUnionBranch39_242

lemma degreeUnionBranch39_243 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 29 10 degreeUnionState39_243 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_244
  · exact degreeUnionBranch39_245
  · exact degreeUnionBranch39_246
  · exact degreeUnionBranch39_247
  · exact degreeUnionBranch39_248
  · exact degreeUnionBranch39_249
  · exact degreeUnionBranch39_250

lemma degreeUnionBranch39_251 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 28 11 degreeUnionState39_251 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 28 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_252
  · exact degreeUnionBranch39_253
  · exact degreeUnionBranch39_254
  · exact degreeUnionBranch39_255
  · exact degreeUnionBranch39_256
  · exact degreeUnionBranch39_257
  · exact degreeUnionBranch39_258
  · exact degreeUnionBranch39_259

lemma degreeUnionBranch39_260 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 27 12 degreeUnionState39_260 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 27 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_261
  · exact degreeUnionBranch39_262
  · exact degreeUnionBranch39_263
  · exact degreeUnionBranch39_264
  · exact degreeUnionBranch39_265
  · exact degreeUnionBranch39_266
  · exact degreeUnionBranch39_267
  · exact degreeUnionBranch39_268
  · exact degreeUnionBranch39_269
  · exact degreeUnionBranch39_270

lemma degreeUnionBranch39_271 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 9 26 13 degreeUnionState39_271 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 13 at hb
  change 26 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_272
  · exact degreeUnionBranch39_273
  · exact degreeUnionBranch39_274
  · exact degreeUnionBranch39_275
  · exact degreeUnionBranch39_276
  · exact degreeUnionBranch39_277
  · exact degreeUnionBranch39_278
  · exact degreeUnionBranch39_279
  · exact degreeUnionBranch39_280
  · exact degreeUnionBranch39_281
  · exact degreeUnionBranch39_282

lemma degreeUnionBranch39_225 : checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) 10 39 38 degreeHalfRegions39 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 38 at hb
  change 39 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch39_226
  · exact degreeUnionBranch39_227
  · exact degreeUnionBranch39_228
  · exact degreeUnionBranch39_229
  · exact degreeUnionBranch39_230
  · exact degreeUnionBranch39_236
  · exact degreeUnionBranch39_243
  · exact degreeUnionBranch39_251
  · exact degreeUnionBranch39_260
  · exact degreeUnionBranch39_271
  · exact degreeUnionBranch39_283
  · exact degreeUnionBranch39_284
  · exact degreeUnionBranch39_285
  · exact degreeUnionBranch39_286
  · exact degreeUnionBranch39_287
  · exact degreeUnionBranch39_288
  · exact degreeUnionBranch39_289
  · exact degreeUnionBranch39_290
  · exact degreeUnionBranch39_291
  · exact degreeUnionBranch39_292
  · exact degreeUnionBranch39_293
  · exact degreeUnionBranch39_294
  · exact degreeUnionBranch39_295
  · exact degreeUnionBranch39_296
  · exact degreeUnionBranch39_297
  · exact degreeUnionBranch39_298
  · exact degreeUnionBranch39_299
  · exact degreeUnionBranch39_300
  · exact degreeUnionBranch39_301
  · exact degreeUnionBranch39_302
  · exact degreeUnionBranch39_303
  · exact degreeUnionBranch39_304
  · exact degreeUnionBranch39_305
  · exact degreeUnionBranch39_306
  · exact degreeUnionBranch39_307

lemma degreeUnionCheck39 : ∀ h ≤ 19,
    checkRegionPrefixes (quickResidual 6 9 degreeQs39 degreeTree39) h 39 38 degreeHalfRegions39 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch39_0
  · exact degreeUnionBranch39_1
  · exact degreeUnionBranch39_2
  · exact degreeUnionBranch39_3
  · exact degreeUnionBranch39_4
  · exact degreeUnionBranch39_5
  · exact degreeUnionBranch39_6
  · exact degreeUnionBranch39_7
  · exact degreeUnionBranch39_8
  · exact degreeUnionBranch39_121
  · exact degreeUnionBranch39_225
  · exact degreeUnionBranch39_308
  · exact degreeUnionBranch39_309
  · exact degreeUnionBranch39_310
  · exact degreeUnionBranch39_311
  · exact degreeUnionBranch39_312
  · exact degreeUnionBranch39_313
  · exact degreeUnionBranch39_314
  · exact degreeUnionBranch39_315
  · exact degreeUnionBranch39_316

lemma degreeHalfCover39 : ∀ R ∈ degreeRegions39,
    R ∈ degreeHalfRegions39 ∨ (R.2,R.1) ∈ degreeHalfRegions39 := by decide +kernel

lemma degreeDiagramRegionsChecked39 : ∀ R ∈ degreeRegions39,
    ∀ μ : YoungDiagram, μ.card = 39 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP39 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck39 degreeHalfHeight39 degreeHalfWidth39
    degreeHalfCover39

end UniversalTensorSquare
end

end OAI
