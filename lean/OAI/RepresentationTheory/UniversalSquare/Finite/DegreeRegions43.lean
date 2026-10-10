import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CheckedUnionSymmetry
import OAI.RepresentationTheory.UniversalSquare.Support.SplitUnionRowChecker
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeLeaves43

namespace OAI

/-! Degree Regions 43. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch43_11 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 35 8 degreeUnionState43_11 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 5 ≤ a at ha
  change a ≤ 8 at hb
  change 35 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_12
  · exact degreeUnionBranch43_13
  · exact degreeUnionBranch43_14
  · exact degreeUnionBranch43_15

lemma degreeUnionBranch43_16 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 34 9 degreeUnionState43_16 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 9 at hb
  change 34 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_17
  · exact degreeUnionBranch43_18
  · exact degreeUnionBranch43_19
  · exact degreeUnionBranch43_20
  · exact degreeUnionBranch43_21

lemma degreeUnionBranch43_22 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 33 10 degreeUnionState43_22 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_23
  · exact degreeUnionBranch43_24
  · exact degreeUnionBranch43_25
  · exact degreeUnionBranch43_26
  · exact degreeUnionBranch43_27
  · exact degreeUnionBranch43_28

lemma degreeUnionBranch43_29 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 32 11 degreeUnionState43_29 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 11 at hb
  change 32 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_30
  · exact degreeUnionBranch43_31
  · exact degreeUnionBranch43_32
  · exact degreeUnionBranch43_33
  · exact degreeUnionBranch43_34
  · exact degreeUnionBranch43_35
  · exact degreeUnionBranch43_36

lemma degreeUnionBranch43_37 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 31 12 degreeUnionState43_37 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_38
  · exact degreeUnionBranch43_39
  · exact degreeUnionBranch43_40
  · exact degreeUnionBranch43_41
  · exact degreeUnionBranch43_42
  · exact degreeUnionBranch43_43
  · exact degreeUnionBranch43_44
  · exact degreeUnionBranch43_45

lemma degreeUnionBranch43_46 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 30 13 degreeUnionState43_46 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 13 at hb
  change 30 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_47
  · exact degreeUnionBranch43_48
  · exact degreeUnionBranch43_49
  · exact degreeUnionBranch43_50
  · exact degreeUnionBranch43_51
  · exact degreeUnionBranch43_52
  · exact degreeUnionBranch43_53
  · exact degreeUnionBranch43_54
  · exact degreeUnionBranch43_55

lemma degreeUnionBranch43_56 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 29 14 degreeUnionState43_56 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 14 at hb
  change 29 ≤ 7*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_57
  · exact degreeUnionBranch43_58
  · exact degreeUnionBranch43_59
  · exact degreeUnionBranch43_60
  · exact degreeUnionBranch43_61
  · exact degreeUnionBranch43_62
  · exact degreeUnionBranch43_63
  · exact degreeUnionBranch43_64
  · exact degreeUnionBranch43_65
  · exact degreeUnionBranch43_66

lemma degreeUnionBranch43_67 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 28 15 degreeUnionState43_67 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 15 at hb
  change 28 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_68
  · exact degreeUnionBranch43_69
  · exact degreeUnionBranch43_70
  · exact degreeUnionBranch43_71
  · exact degreeUnionBranch43_72
  · exact degreeUnionBranch43_73
  · exact degreeUnionBranch43_74
  · exact degreeUnionBranch43_75
  · exact degreeUnionBranch43_76
  · exact degreeUnionBranch43_77
  · exact degreeUnionBranch43_78
  · exact degreeUnionBranch43_79

lemma degreeUnionBranch43_80 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 27 16 degreeUnionState43_80 [16] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 16 at hb
  change 27 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_81
  · exact degreeUnionBranch43_82
  · exact degreeUnionBranch43_83
  · exact degreeUnionBranch43_84
  · exact degreeUnionBranch43_85
  · exact degreeUnionBranch43_86
  · exact degreeUnionBranch43_87
  · exact degreeUnionBranch43_88
  · exact degreeUnionBranch43_89
  · exact degreeUnionBranch43_90
  · exact degreeUnionBranch43_91
  · exact degreeUnionBranch43_92
  · exact degreeUnionBranch43_93

lemma degreeUnionBranch43_94 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 26 17 degreeUnionState43_94 [17] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 17 at hb
  change 26 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_95
  · exact degreeUnionBranch43_96
  · exact degreeUnionBranch43_97
  · exact degreeUnionBranch43_98
  · exact degreeUnionBranch43_99
  · exact degreeUnionBranch43_100
  · exact degreeUnionBranch43_101
  · exact degreeUnionBranch43_102
  · exact degreeUnionBranch43_103
  · exact degreeUnionBranch43_104
  · exact degreeUnionBranch43_105
  · exact degreeUnionBranch43_106
  · exact degreeUnionBranch43_107
  · exact degreeUnionBranch43_108

lemma degreeUnionBranch43_109 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 25 18 degreeUnionState43_109 [18] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 18 at hb
  change 25 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_110
  · exact degreeUnionBranch43_111
  · exact degreeUnionBranch43_112
  · exact degreeUnionBranch43_113
  · exact degreeUnionBranch43_114
  · exact degreeUnionBranch43_115
  · exact degreeUnionBranch43_116
  · exact degreeUnionBranch43_117
  · exact degreeUnionBranch43_118
  · exact degreeUnionBranch43_119
  · exact degreeUnionBranch43_120
  · exact degreeUnionBranch43_121
  · exact degreeUnionBranch43_122
  · exact degreeUnionBranch43_123
  · exact degreeUnionBranch43_124

lemma degreeUnionBranch43_125 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 24 19 degreeUnionState43_125 [19] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 19 at hb
  change 24 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_126
  · exact degreeUnionBranch43_127
  · exact degreeUnionBranch43_128
  · exact degreeUnionBranch43_129
  · exact degreeUnionBranch43_130
  · exact degreeUnionBranch43_131
  · exact degreeUnionBranch43_132
  · exact degreeUnionBranch43_133
  · exact degreeUnionBranch43_134
  · exact degreeUnionBranch43_135
  · exact degreeUnionBranch43_136
  · exact degreeUnionBranch43_137
  · exact degreeUnionBranch43_138
  · exact degreeUnionBranch43_139
  · exact degreeUnionBranch43_140
  · exact degreeUnionBranch43_141

lemma degreeUnionBranch43_142 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 23 20 degreeUnionState43_142 [20] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 20 at hb
  change 23 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_143
  · exact degreeUnionBranch43_144
  · exact degreeUnionBranch43_145
  · exact degreeUnionBranch43_146
  · exact degreeUnionBranch43_147
  · exact degreeUnionBranch43_148
  · exact degreeUnionBranch43_149
  · exact degreeUnionBranch43_150
  · exact degreeUnionBranch43_151
  · exact degreeUnionBranch43_152
  · exact degreeUnionBranch43_153
  · exact degreeUnionBranch43_154
  · exact degreeUnionBranch43_155
  · exact degreeUnionBranch43_156
  · exact degreeUnionBranch43_157
  · exact degreeUnionBranch43_158
  · exact degreeUnionBranch43_159

lemma degreeUnionBranch43_8 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 5 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 8*a at hn
  have hlo : 6 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_9
  · exact degreeUnionBranch43_10
  · exact degreeUnionBranch43_11
  · exact degreeUnionBranch43_16
  · exact degreeUnionBranch43_22
  · exact degreeUnionBranch43_29
  · exact degreeUnionBranch43_37
  · exact degreeUnionBranch43_46
  · exact degreeUnionBranch43_56
  · exact degreeUnionBranch43_67
  · exact degreeUnionBranch43_80
  · exact degreeUnionBranch43_94
  · exact degreeUnionBranch43_109
  · exact degreeUnionBranch43_125
  · exact degreeUnionBranch43_142
  · exact degreeUnionBranch43_160
  · exact degreeUnionBranch43_161
  · exact degreeUnionBranch43_162
  · exact degreeUnionBranch43_163
  · exact degreeUnionBranch43_164
  · exact degreeUnionBranch43_165
  · exact degreeUnionBranch43_166
  · exact degreeUnionBranch43_167
  · exact degreeUnionBranch43_168
  · exact degreeUnionBranch43_169
  · exact degreeUnionBranch43_170
  · exact degreeUnionBranch43_171
  · exact degreeUnionBranch43_172
  · exact degreeUnionBranch43_173
  · exact degreeUnionBranch43_174
  · exact degreeUnionBranch43_175
  · exact degreeUnionBranch43_176
  · exact degreeUnionBranch43_177
  · exact degreeUnionBranch43_178
  · exact degreeUnionBranch43_179
  · exact degreeUnionBranch43_180
  · exact degreeUnionBranch43_181

lemma degreeUnionBranch43_186 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 35 8 degreeUnionState43_186 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 8 at hb
  change 35 ≤ 8*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_187
  · exact degreeUnionBranch43_188
  · exact degreeUnionBranch43_189
  · exact degreeUnionBranch43_190

lemma degreeUnionBranch43_196 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 7 25 9 degreeUnionState43_196 [9,9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 25 ≤ 7*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_197
  · exact degreeUnionBranch43_198
  · exact degreeUnionBranch43_199
  · exact degreeUnionBranch43_200
  · exact degreeUnionBranch43_201
  · exact degreeUnionBranch43_202

lemma degreeUnionBranch43_191 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 34 9 degreeUnionState43_191 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 9 at hb
  change 34 ≤ 8*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_192
  · exact degreeUnionBranch43_193
  · exact degreeUnionBranch43_194
  · exact degreeUnionBranch43_195
  · exact degreeUnionBranch43_196

lemma degreeUnionBranch43_203 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 33 10 degreeUnionState43_203 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 8*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_204
  · exact degreeUnionBranch43_205
  · exact degreeUnionBranch43_206
  · exact degreeUnionBranch43_207
  · exact degreeUnionBranch43_208
  · exact degreeUnionBranch43_209

lemma degreeUnionBranch43_210 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 32 11 degreeUnionState43_210 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 11 at hb
  change 32 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_211
  · exact degreeUnionBranch43_212
  · exact degreeUnionBranch43_213
  · exact degreeUnionBranch43_214
  · exact degreeUnionBranch43_215
  · exact degreeUnionBranch43_216
  · exact degreeUnionBranch43_217
  · exact degreeUnionBranch43_218

lemma degreeUnionBranch43_219 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 31 12 degreeUnionState43_219 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_220
  · exact degreeUnionBranch43_221
  · exact degreeUnionBranch43_222
  · exact degreeUnionBranch43_223
  · exact degreeUnionBranch43_224
  · exact degreeUnionBranch43_225
  · exact degreeUnionBranch43_226
  · exact degreeUnionBranch43_227
  · exact degreeUnionBranch43_228

lemma degreeUnionBranch43_229 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 30 13 degreeUnionState43_229 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 30 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_230
  · exact degreeUnionBranch43_231
  · exact degreeUnionBranch43_232
  · exact degreeUnionBranch43_233
  · exact degreeUnionBranch43_234
  · exact degreeUnionBranch43_235
  · exact degreeUnionBranch43_236
  · exact degreeUnionBranch43_237
  · exact degreeUnionBranch43_238
  · exact degreeUnionBranch43_239

lemma degreeUnionBranch43_240 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 29 14 degreeUnionState43_240 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 29 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_241
  · exact degreeUnionBranch43_242
  · exact degreeUnionBranch43_243
  · exact degreeUnionBranch43_244
  · exact degreeUnionBranch43_245
  · exact degreeUnionBranch43_246
  · exact degreeUnionBranch43_247
  · exact degreeUnionBranch43_248
  · exact degreeUnionBranch43_249
  · exact degreeUnionBranch43_250
  · exact degreeUnionBranch43_251

lemma degreeUnionBranch43_252 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 28 15 degreeUnionState43_252 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 15 at hb
  change 28 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_253
  · exact degreeUnionBranch43_254
  · exact degreeUnionBranch43_255
  · exact degreeUnionBranch43_256
  · exact degreeUnionBranch43_257
  · exact degreeUnionBranch43_258
  · exact degreeUnionBranch43_259
  · exact degreeUnionBranch43_260
  · exact degreeUnionBranch43_261
  · exact degreeUnionBranch43_262
  · exact degreeUnionBranch43_263
  · exact degreeUnionBranch43_264

lemma degreeUnionBranch43_265 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 27 16 degreeUnionState43_265 [16] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 16 at hb
  change 27 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_266
  · exact degreeUnionBranch43_267
  · exact degreeUnionBranch43_268
  · exact degreeUnionBranch43_269
  · exact degreeUnionBranch43_270
  · exact degreeUnionBranch43_271
  · exact degreeUnionBranch43_272
  · exact degreeUnionBranch43_273
  · exact degreeUnionBranch43_274
  · exact degreeUnionBranch43_275
  · exact degreeUnionBranch43_276
  · exact degreeUnionBranch43_277
  · exact degreeUnionBranch43_278

lemma degreeUnionBranch43_279 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 26 17 degreeUnionState43_279 [17] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 17 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_280
  · exact degreeUnionBranch43_281
  · exact degreeUnionBranch43_282
  · exact degreeUnionBranch43_283
  · exact degreeUnionBranch43_284
  · exact degreeUnionBranch43_285
  · exact degreeUnionBranch43_286
  · exact degreeUnionBranch43_287
  · exact degreeUnionBranch43_288
  · exact degreeUnionBranch43_289
  · exact degreeUnionBranch43_290
  · exact degreeUnionBranch43_291
  · exact degreeUnionBranch43_292
  · exact degreeUnionBranch43_293

lemma degreeUnionBranch43_294 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 25 18 degreeUnionState43_294 [18] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 18 at hb
  change 25 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_295
  · exact degreeUnionBranch43_296
  · exact degreeUnionBranch43_297
  · exact degreeUnionBranch43_298
  · exact degreeUnionBranch43_299
  · exact degreeUnionBranch43_300
  · exact degreeUnionBranch43_301
  · exact degreeUnionBranch43_302
  · exact degreeUnionBranch43_303
  · exact degreeUnionBranch43_304
  · exact degreeUnionBranch43_305
  · exact degreeUnionBranch43_306
  · exact degreeUnionBranch43_307
  · exact degreeUnionBranch43_308
  · exact degreeUnionBranch43_309

lemma degreeUnionBranch43_310 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 24 19 degreeUnionState43_310 [19] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 19 at hb
  change 24 ≤ 8*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_311
  · exact degreeUnionBranch43_312
  · exact degreeUnionBranch43_313
  · exact degreeUnionBranch43_314
  · exact degreeUnionBranch43_315
  · exact degreeUnionBranch43_316
  · exact degreeUnionBranch43_317
  · exact degreeUnionBranch43_318
  · exact degreeUnionBranch43_319
  · exact degreeUnionBranch43_320
  · exact degreeUnionBranch43_321
  · exact degreeUnionBranch43_322
  · exact degreeUnionBranch43_323
  · exact degreeUnionBranch43_324
  · exact degreeUnionBranch43_325
  · exact degreeUnionBranch43_326
  · exact degreeUnionBranch43_327

lemma degreeUnionBranch43_182 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 9*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_183
  · exact degreeUnionBranch43_184
  · exact degreeUnionBranch43_185
  · exact degreeUnionBranch43_186
  · exact degreeUnionBranch43_191
  · exact degreeUnionBranch43_203
  · exact degreeUnionBranch43_210
  · exact degreeUnionBranch43_219
  · exact degreeUnionBranch43_229
  · exact degreeUnionBranch43_240
  · exact degreeUnionBranch43_252
  · exact degreeUnionBranch43_265
  · exact degreeUnionBranch43_279
  · exact degreeUnionBranch43_294
  · exact degreeUnionBranch43_310
  · exact degreeUnionBranch43_328
  · exact degreeUnionBranch43_329
  · exact degreeUnionBranch43_330
  · exact degreeUnionBranch43_331
  · exact degreeUnionBranch43_332
  · exact degreeUnionBranch43_333
  · exact degreeUnionBranch43_334
  · exact degreeUnionBranch43_335
  · exact degreeUnionBranch43_336
  · exact degreeUnionBranch43_337
  · exact degreeUnionBranch43_338
  · exact degreeUnionBranch43_339
  · exact degreeUnionBranch43_340
  · exact degreeUnionBranch43_341
  · exact degreeUnionBranch43_342
  · exact degreeUnionBranch43_343
  · exact degreeUnionBranch43_344
  · exact degreeUnionBranch43_345
  · exact degreeUnionBranch43_346
  · exact degreeUnionBranch43_347
  · exact degreeUnionBranch43_348
  · exact degreeUnionBranch43_349
  · exact degreeUnionBranch43_350

lemma degreeUnionBranch43_360 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 27 8 degreeUnionState43_360 [8,8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 27 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_361
  · exact degreeUnionBranch43_362
  · exact degreeUnionBranch43_363
  · exact degreeUnionBranch43_364
  · exact degreeUnionBranch43_365

lemma degreeUnionBranch43_355 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 35 8 degreeUnionState43_355 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 35 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_356
  · exact degreeUnionBranch43_357
  · exact degreeUnionBranch43_358
  · exact degreeUnionBranch43_359
  · exact degreeUnionBranch43_360

lemma degreeUnionBranch43_371 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 26 8 degreeUnionState43_371 [8,9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 26 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_372
  · exact degreeUnionBranch43_373
  · exact degreeUnionBranch43_374
  · exact degreeUnionBranch43_375
  · exact degreeUnionBranch43_376

lemma degreeUnionBranch43_377 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 8 25 9 degreeUnionState43_377 [9,9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 25 ≤ 8*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_378
  · exact degreeUnionBranch43_379
  · exact degreeUnionBranch43_380
  · exact degreeUnionBranch43_381
  · exact degreeUnionBranch43_382
  · exact degreeUnionBranch43_383

lemma degreeUnionBranch43_366 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 34 9 degreeUnionState43_366 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 34 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_367
  · exact degreeUnionBranch43_368
  · exact degreeUnionBranch43_369
  · exact degreeUnionBranch43_370
  · exact degreeUnionBranch43_371
  · exact degreeUnionBranch43_377

lemma degreeUnionBranch43_384 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 33 10 degreeUnionState43_384 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_385
  · exact degreeUnionBranch43_386
  · exact degreeUnionBranch43_387
  · exact degreeUnionBranch43_388
  · exact degreeUnionBranch43_389
  · exact degreeUnionBranch43_390
  · exact degreeUnionBranch43_391

lemma degreeUnionBranch43_392 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 32 11 degreeUnionState43_392 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 32 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_393
  · exact degreeUnionBranch43_394
  · exact degreeUnionBranch43_395
  · exact degreeUnionBranch43_396
  · exact degreeUnionBranch43_397
  · exact degreeUnionBranch43_398
  · exact degreeUnionBranch43_399
  · exact degreeUnionBranch43_400

lemma degreeUnionBranch43_401 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 31 12 degreeUnionState43_401 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_402
  · exact degreeUnionBranch43_403
  · exact degreeUnionBranch43_404
  · exact degreeUnionBranch43_405
  · exact degreeUnionBranch43_406
  · exact degreeUnionBranch43_407
  · exact degreeUnionBranch43_408
  · exact degreeUnionBranch43_409
  · exact degreeUnionBranch43_410

lemma degreeUnionBranch43_411 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 30 13 degreeUnionState43_411 [13] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 13 at hb
  change 30 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_412
  · exact degreeUnionBranch43_413
  · exact degreeUnionBranch43_414
  · exact degreeUnionBranch43_415
  · exact degreeUnionBranch43_416
  · exact degreeUnionBranch43_417
  · exact degreeUnionBranch43_418
  · exact degreeUnionBranch43_419
  · exact degreeUnionBranch43_420
  · exact degreeUnionBranch43_421

lemma degreeUnionBranch43_422 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 29 14 degreeUnionState43_422 [14] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 14 at hb
  change 29 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_423
  · exact degreeUnionBranch43_424
  · exact degreeUnionBranch43_425
  · exact degreeUnionBranch43_426
  · exact degreeUnionBranch43_427
  · exact degreeUnionBranch43_428
  · exact degreeUnionBranch43_429
  · exact degreeUnionBranch43_430
  · exact degreeUnionBranch43_431
  · exact degreeUnionBranch43_432
  · exact degreeUnionBranch43_433

lemma degreeUnionBranch43_434 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 28 15 degreeUnionState43_434 [15] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 15 at hb
  change 28 ≤ 9*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_435
  · exact degreeUnionBranch43_436
  · exact degreeUnionBranch43_437
  · exact degreeUnionBranch43_438
  · exact degreeUnionBranch43_439
  · exact degreeUnionBranch43_440
  · exact degreeUnionBranch43_441
  · exact degreeUnionBranch43_442
  · exact degreeUnionBranch43_443
  · exact degreeUnionBranch43_444
  · exact degreeUnionBranch43_445
  · exact degreeUnionBranch43_446

lemma degreeUnionBranch43_447 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 27 16 degreeUnionState43_447 [16] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 16 at hb
  change 27 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_448
  · exact degreeUnionBranch43_449
  · exact degreeUnionBranch43_450
  · exact degreeUnionBranch43_451
  · exact degreeUnionBranch43_452
  · exact degreeUnionBranch43_453
  · exact degreeUnionBranch43_454
  · exact degreeUnionBranch43_455
  · exact degreeUnionBranch43_456
  · exact degreeUnionBranch43_457
  · exact degreeUnionBranch43_458
  · exact degreeUnionBranch43_459
  · exact degreeUnionBranch43_460
  · exact degreeUnionBranch43_461

lemma degreeUnionBranch43_462 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 26 17 degreeUnionState43_462 [17] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 17 at hb
  change 26 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_463
  · exact degreeUnionBranch43_464
  · exact degreeUnionBranch43_465
  · exact degreeUnionBranch43_466
  · exact degreeUnionBranch43_467
  · exact degreeUnionBranch43_468
  · exact degreeUnionBranch43_469
  · exact degreeUnionBranch43_470
  · exact degreeUnionBranch43_471
  · exact degreeUnionBranch43_472
  · exact degreeUnionBranch43_473
  · exact degreeUnionBranch43_474
  · exact degreeUnionBranch43_475
  · exact degreeUnionBranch43_476
  · exact degreeUnionBranch43_477

lemma degreeUnionBranch43_478 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 25 18 degreeUnionState43_478 [18] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 18 at hb
  change 25 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_479
  · exact degreeUnionBranch43_480
  · exact degreeUnionBranch43_481
  · exact degreeUnionBranch43_482
  · exact degreeUnionBranch43_483
  · exact degreeUnionBranch43_484
  · exact degreeUnionBranch43_485
  · exact degreeUnionBranch43_486
  · exact degreeUnionBranch43_487
  · exact degreeUnionBranch43_488
  · exact degreeUnionBranch43_489
  · exact degreeUnionBranch43_490
  · exact degreeUnionBranch43_491
  · exact degreeUnionBranch43_492
  · exact degreeUnionBranch43_493
  · exact degreeUnionBranch43_494

lemma degreeUnionBranch43_495 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 9 24 19 degreeUnionState43_495 [19] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 19 at hb
  change 24 ≤ 9*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_496
  · exact degreeUnionBranch43_497
  · exact degreeUnionBranch43_498
  · exact degreeUnionBranch43_499
  · exact degreeUnionBranch43_500
  · exact degreeUnionBranch43_501
  · exact degreeUnionBranch43_502
  · exact degreeUnionBranch43_503
  · exact degreeUnionBranch43_504
  · exact degreeUnionBranch43_505
  · exact degreeUnionBranch43_506
  · exact degreeUnionBranch43_507
  · exact degreeUnionBranch43_508
  · exact degreeUnionBranch43_509
  · exact degreeUnionBranch43_510
  · exact degreeUnionBranch43_511
  · exact degreeUnionBranch43_512

lemma degreeUnionBranch43_351 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 4 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 10*a at hn
  have hlo : 5 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_352
  · exact degreeUnionBranch43_353
  · exact degreeUnionBranch43_354
  · exact degreeUnionBranch43_355
  · exact degreeUnionBranch43_366
  · exact degreeUnionBranch43_384
  · exact degreeUnionBranch43_392
  · exact degreeUnionBranch43_401
  · exact degreeUnionBranch43_411
  · exact degreeUnionBranch43_422
  · exact degreeUnionBranch43_434
  · exact degreeUnionBranch43_447
  · exact degreeUnionBranch43_462
  · exact degreeUnionBranch43_478
  · exact degreeUnionBranch43_495
  · exact degreeUnionBranch43_513
  · exact degreeUnionBranch43_514
  · exact degreeUnionBranch43_515
  · exact degreeUnionBranch43_516
  · exact degreeUnionBranch43_517
  · exact degreeUnionBranch43_518
  · exact degreeUnionBranch43_519
  · exact degreeUnionBranch43_520
  · exact degreeUnionBranch43_521
  · exact degreeUnionBranch43_522
  · exact degreeUnionBranch43_523
  · exact degreeUnionBranch43_524
  · exact degreeUnionBranch43_525
  · exact degreeUnionBranch43_526
  · exact degreeUnionBranch43_527
  · exact degreeUnionBranch43_528
  · exact degreeUnionBranch43_529
  · exact degreeUnionBranch43_530
  · exact degreeUnionBranch43_531
  · exact degreeUnionBranch43_532
  · exact degreeUnionBranch43_533
  · exact degreeUnionBranch43_534
  · exact degreeUnionBranch43_535

lemma degreeUnionBranch43_541 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 35 8 degreeUnionState43_541 [8] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 8 at hb
  change 35 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_542
  · exact degreeUnionBranch43_543
  · exact degreeUnionBranch43_544
  · exact degreeUnionBranch43_545
  · exact degreeUnionBranch43_546

lemma degreeUnionBranch43_547 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 34 9 degreeUnionState43_547 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 34 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_548
  · exact degreeUnionBranch43_549
  · exact degreeUnionBranch43_550
  · exact degreeUnionBranch43_551
  · exact degreeUnionBranch43_552
  · exact degreeUnionBranch43_553

lemma degreeUnionBranch43_554 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 33 10 degreeUnionState43_554 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_555
  · exact degreeUnionBranch43_556
  · exact degreeUnionBranch43_557
  · exact degreeUnionBranch43_558
  · exact degreeUnionBranch43_559
  · exact degreeUnionBranch43_560
  · exact degreeUnionBranch43_561

lemma degreeUnionBranch43_562 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 32 11 degreeUnionState43_562 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 11 at hb
  change 32 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_563
  · exact degreeUnionBranch43_564
  · exact degreeUnionBranch43_565
  · exact degreeUnionBranch43_566
  · exact degreeUnionBranch43_567
  · exact degreeUnionBranch43_568
  · exact degreeUnionBranch43_569
  · exact degreeUnionBranch43_570

lemma degreeUnionBranch43_571 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 10 31 12 degreeUnionState43_571 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 10*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_572
  · exact degreeUnionBranch43_573
  · exact degreeUnionBranch43_574
  · exact degreeUnionBranch43_575
  · exact degreeUnionBranch43_576
  · exact degreeUnionBranch43_577
  · exact degreeUnionBranch43_578
  · exact degreeUnionBranch43_579
  · exact degreeUnionBranch43_580

lemma degreeUnionBranch43_536 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_537
  · exact degreeUnionBranch43_538
  · exact degreeUnionBranch43_539
  · exact degreeUnionBranch43_540
  · exact degreeUnionBranch43_541
  · exact degreeUnionBranch43_547
  · exact degreeUnionBranch43_554
  · exact degreeUnionBranch43_562
  · exact degreeUnionBranch43_571
  · exact degreeUnionBranch43_581
  · exact degreeUnionBranch43_582
  · exact degreeUnionBranch43_583
  · exact degreeUnionBranch43_584
  · exact degreeUnionBranch43_585
  · exact degreeUnionBranch43_586
  · exact degreeUnionBranch43_587
  · exact degreeUnionBranch43_588
  · exact degreeUnionBranch43_589
  · exact degreeUnionBranch43_590
  · exact degreeUnionBranch43_591
  · exact degreeUnionBranch43_592
  · exact degreeUnionBranch43_593
  · exact degreeUnionBranch43_594
  · exact degreeUnionBranch43_595
  · exact degreeUnionBranch43_596
  · exact degreeUnionBranch43_597
  · exact degreeUnionBranch43_598
  · exact degreeUnionBranch43_599
  · exact degreeUnionBranch43_600
  · exact degreeUnionBranch43_601
  · exact degreeUnionBranch43_602
  · exact degreeUnionBranch43_603
  · exact degreeUnionBranch43_604
  · exact degreeUnionBranch43_605
  · exact degreeUnionBranch43_606
  · exact degreeUnionBranch43_607
  · exact degreeUnionBranch43_608
  · exact degreeUnionBranch43_609
  · exact degreeUnionBranch43_610

lemma degreeUnionBranch43_617 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 34 9 degreeUnionState43_617 [9] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 9 at hb
  change 34 ≤ 11*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_618
  · exact degreeUnionBranch43_619
  · exact degreeUnionBranch43_620
  · exact degreeUnionBranch43_621
  · exact degreeUnionBranch43_622
  · exact degreeUnionBranch43_623

lemma degreeUnionBranch43_624 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 33 10 degreeUnionState43_624 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_625
  · exact degreeUnionBranch43_626
  · exact degreeUnionBranch43_627
  · exact degreeUnionBranch43_628
  · exact degreeUnionBranch43_629
  · exact degreeUnionBranch43_630
  · exact degreeUnionBranch43_631
  · exact degreeUnionBranch43_632

lemma degreeUnionBranch43_633 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 32 11 degreeUnionState43_633 [11] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 11 at hb
  change 32 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_634
  · exact degreeUnionBranch43_635
  · exact degreeUnionBranch43_636
  · exact degreeUnionBranch43_637
  · exact degreeUnionBranch43_638
  · exact degreeUnionBranch43_639
  · exact degreeUnionBranch43_640
  · exact degreeUnionBranch43_641
  · exact degreeUnionBranch43_642

lemma degreeUnionBranch43_643 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 11 31 12 degreeUnionState43_643 [12] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 12 at hb
  change 31 ≤ 11*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_644
  · exact degreeUnionBranch43_645
  · exact degreeUnionBranch43_646
  · exact degreeUnionBranch43_647
  · exact degreeUnionBranch43_648
  · exact degreeUnionBranch43_649
  · exact degreeUnionBranch43_650
  · exact degreeUnionBranch43_651
  · exact degreeUnionBranch43_652
  · exact degreeUnionBranch43_653

lemma degreeUnionBranch43_611 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 12*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_612
  · exact degreeUnionBranch43_613
  · exact degreeUnionBranch43_614
  · exact degreeUnionBranch43_615
  · exact degreeUnionBranch43_616
  · exact degreeUnionBranch43_617
  · exact degreeUnionBranch43_624
  · exact degreeUnionBranch43_633
  · exact degreeUnionBranch43_643
  · exact degreeUnionBranch43_654
  · exact degreeUnionBranch43_655
  · exact degreeUnionBranch43_656
  · exact degreeUnionBranch43_657
  · exact degreeUnionBranch43_658
  · exact degreeUnionBranch43_659
  · exact degreeUnionBranch43_660
  · exact degreeUnionBranch43_661
  · exact degreeUnionBranch43_662
  · exact degreeUnionBranch43_663
  · exact degreeUnionBranch43_664
  · exact degreeUnionBranch43_665
  · exact degreeUnionBranch43_666
  · exact degreeUnionBranch43_667
  · exact degreeUnionBranch43_668
  · exact degreeUnionBranch43_669
  · exact degreeUnionBranch43_670
  · exact degreeUnionBranch43_671
  · exact degreeUnionBranch43_672
  · exact degreeUnionBranch43_673
  · exact degreeUnionBranch43_674
  · exact degreeUnionBranch43_675
  · exact degreeUnionBranch43_676
  · exact degreeUnionBranch43_677
  · exact degreeUnionBranch43_678
  · exact degreeUnionBranch43_679
  · exact degreeUnionBranch43_680
  · exact degreeUnionBranch43_681
  · exact degreeUnionBranch43_682
  · exact degreeUnionBranch43_683

lemma degreeUnionBranch43_691 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 12 33 10 degreeUnionState43_691 [10] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 10 at hb
  change 33 ≤ 12*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_692
  · exact degreeUnionBranch43_693
  · exact degreeUnionBranch43_694
  · exact degreeUnionBranch43_695
  · exact degreeUnionBranch43_696
  · exact degreeUnionBranch43_697
  · exact degreeUnionBranch43_698
  · exact degreeUnionBranch43_699

lemma degreeUnionBranch43_684 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 13 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 13*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_685
  · exact degreeUnionBranch43_686
  · exact degreeUnionBranch43_687
  · exact degreeUnionBranch43_688
  · exact degreeUnionBranch43_689
  · exact degreeUnionBranch43_690
  · exact degreeUnionBranch43_691
  · exact degreeUnionBranch43_700
  · exact degreeUnionBranch43_701
  · exact degreeUnionBranch43_702
  · exact degreeUnionBranch43_703
  · exact degreeUnionBranch43_704
  · exact degreeUnionBranch43_705
  · exact degreeUnionBranch43_706
  · exact degreeUnionBranch43_707
  · exact degreeUnionBranch43_708
  · exact degreeUnionBranch43_709
  · exact degreeUnionBranch43_710
  · exact degreeUnionBranch43_711
  · exact degreeUnionBranch43_712
  · exact degreeUnionBranch43_713
  · exact degreeUnionBranch43_714
  · exact degreeUnionBranch43_715
  · exact degreeUnionBranch43_716
  · exact degreeUnionBranch43_717
  · exact degreeUnionBranch43_718
  · exact degreeUnionBranch43_719
  · exact degreeUnionBranch43_720
  · exact degreeUnionBranch43_721
  · exact degreeUnionBranch43_722
  · exact degreeUnionBranch43_723
  · exact degreeUnionBranch43_724
  · exact degreeUnionBranch43_725
  · exact degreeUnionBranch43_726
  · exact degreeUnionBranch43_727
  · exact degreeUnionBranch43_728
  · exact degreeUnionBranch43_729
  · exact degreeUnionBranch43_730
  · exact degreeUnionBranch43_731

lemma degreeUnionBranch43_732 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 14 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 3 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 14*a at hn
  have hlo : 4 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_733
  · exact degreeUnionBranch43_734
  · exact degreeUnionBranch43_735
  · exact degreeUnionBranch43_736
  · exact degreeUnionBranch43_737
  · exact degreeUnionBranch43_738
  · exact degreeUnionBranch43_739
  · exact degreeUnionBranch43_740
  · exact degreeUnionBranch43_741
  · exact degreeUnionBranch43_742
  · exact degreeUnionBranch43_743
  · exact degreeUnionBranch43_744
  · exact degreeUnionBranch43_745
  · exact degreeUnionBranch43_746
  · exact degreeUnionBranch43_747
  · exact degreeUnionBranch43_748
  · exact degreeUnionBranch43_749
  · exact degreeUnionBranch43_750
  · exact degreeUnionBranch43_751
  · exact degreeUnionBranch43_752
  · exact degreeUnionBranch43_753
  · exact degreeUnionBranch43_754
  · exact degreeUnionBranch43_755
  · exact degreeUnionBranch43_756
  · exact degreeUnionBranch43_757
  · exact degreeUnionBranch43_758
  · exact degreeUnionBranch43_759
  · exact degreeUnionBranch43_760
  · exact degreeUnionBranch43_761
  · exact degreeUnionBranch43_762
  · exact degreeUnionBranch43_763
  · exact degreeUnionBranch43_764
  · exact degreeUnionBranch43_765
  · exact degreeUnionBranch43_766
  · exact degreeUnionBranch43_767
  · exact degreeUnionBranch43_768
  · exact degreeUnionBranch43_769
  · exact degreeUnionBranch43_770
  · exact degreeUnionBranch43_771

lemma degreeUnionBranch43_772 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 15 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 15*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_773
  · exact degreeUnionBranch43_774
  · exact degreeUnionBranch43_775
  · exact degreeUnionBranch43_776
  · exact degreeUnionBranch43_777
  · exact degreeUnionBranch43_778
  · exact degreeUnionBranch43_779
  · exact degreeUnionBranch43_780
  · exact degreeUnionBranch43_781
  · exact degreeUnionBranch43_782
  · exact degreeUnionBranch43_783
  · exact degreeUnionBranch43_784
  · exact degreeUnionBranch43_785
  · exact degreeUnionBranch43_786
  · exact degreeUnionBranch43_787
  · exact degreeUnionBranch43_788
  · exact degreeUnionBranch43_789
  · exact degreeUnionBranch43_790
  · exact degreeUnionBranch43_791
  · exact degreeUnionBranch43_792
  · exact degreeUnionBranch43_793
  · exact degreeUnionBranch43_794
  · exact degreeUnionBranch43_795
  · exact degreeUnionBranch43_796
  · exact degreeUnionBranch43_797
  · exact degreeUnionBranch43_798
  · exact degreeUnionBranch43_799
  · exact degreeUnionBranch43_800
  · exact degreeUnionBranch43_801
  · exact degreeUnionBranch43_802
  · exact degreeUnionBranch43_803
  · exact degreeUnionBranch43_804
  · exact degreeUnionBranch43_805
  · exact degreeUnionBranch43_806
  · exact degreeUnionBranch43_807
  · exact degreeUnionBranch43_808
  · exact degreeUnionBranch43_809
  · exact degreeUnionBranch43_810
  · exact degreeUnionBranch43_811
  · exact degreeUnionBranch43_812

lemma degreeUnionBranch43_813 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 16 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 16*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_814
  · exact degreeUnionBranch43_815
  · exact degreeUnionBranch43_816
  · exact degreeUnionBranch43_817
  · exact degreeUnionBranch43_818
  · exact degreeUnionBranch43_819
  · exact degreeUnionBranch43_820
  · exact degreeUnionBranch43_821
  · exact degreeUnionBranch43_822
  · exact degreeUnionBranch43_823
  · exact degreeUnionBranch43_824
  · exact degreeUnionBranch43_825
  · exact degreeUnionBranch43_826
  · exact degreeUnionBranch43_827
  · exact degreeUnionBranch43_828
  · exact degreeUnionBranch43_829
  · exact degreeUnionBranch43_830
  · exact degreeUnionBranch43_831
  · exact degreeUnionBranch43_832
  · exact degreeUnionBranch43_833
  · exact degreeUnionBranch43_834
  · exact degreeUnionBranch43_835
  · exact degreeUnionBranch43_836
  · exact degreeUnionBranch43_837
  · exact degreeUnionBranch43_838
  · exact degreeUnionBranch43_839
  · exact degreeUnionBranch43_840
  · exact degreeUnionBranch43_841
  · exact degreeUnionBranch43_842
  · exact degreeUnionBranch43_843
  · exact degreeUnionBranch43_844
  · exact degreeUnionBranch43_845
  · exact degreeUnionBranch43_846
  · exact degreeUnionBranch43_847
  · exact degreeUnionBranch43_848
  · exact degreeUnionBranch43_849
  · exact degreeUnionBranch43_850
  · exact degreeUnionBranch43_851
  · exact degreeUnionBranch43_852
  · exact degreeUnionBranch43_853

lemma degreeUnionBranch43_854 : checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) 17 43 42 degreeHalfRegions43 [] = true := by
  apply checkRegionPrefixes_step
  intro a ha hb hn
  change 2 ≤ a at ha
  change a ≤ 42 at hb
  change 43 ≤ 17*a at hn
  have hlo : 3 ≤ a := by omega
  interval_cases a
  · exact degreeUnionBranch43_855
  · exact degreeUnionBranch43_856
  · exact degreeUnionBranch43_857
  · exact degreeUnionBranch43_858
  · exact degreeUnionBranch43_859
  · exact degreeUnionBranch43_860
  · exact degreeUnionBranch43_861
  · exact degreeUnionBranch43_862
  · exact degreeUnionBranch43_863
  · exact degreeUnionBranch43_864
  · exact degreeUnionBranch43_865
  · exact degreeUnionBranch43_866
  · exact degreeUnionBranch43_867
  · exact degreeUnionBranch43_868
  · exact degreeUnionBranch43_869
  · exact degreeUnionBranch43_870
  · exact degreeUnionBranch43_871
  · exact degreeUnionBranch43_872
  · exact degreeUnionBranch43_873
  · exact degreeUnionBranch43_874
  · exact degreeUnionBranch43_875
  · exact degreeUnionBranch43_876
  · exact degreeUnionBranch43_877
  · exact degreeUnionBranch43_878
  · exact degreeUnionBranch43_879
  · exact degreeUnionBranch43_880
  · exact degreeUnionBranch43_881
  · exact degreeUnionBranch43_882
  · exact degreeUnionBranch43_883
  · exact degreeUnionBranch43_884
  · exact degreeUnionBranch43_885
  · exact degreeUnionBranch43_886
  · exact degreeUnionBranch43_887
  · exact degreeUnionBranch43_888
  · exact degreeUnionBranch43_889
  · exact degreeUnionBranch43_890
  · exact degreeUnionBranch43_891
  · exact degreeUnionBranch43_892
  · exact degreeUnionBranch43_893
  · exact degreeUnionBranch43_894

lemma degreeUnionCheck43 : ∀ h ≤ 23,
    checkRegionPrefixes (quickResidual 6 11 degreeQs43 degreeTree43) h 43 42 degreeHalfRegions43 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch43_0
  · exact degreeUnionBranch43_1
  · exact degreeUnionBranch43_2
  · exact degreeUnionBranch43_3
  · exact degreeUnionBranch43_4
  · exact degreeUnionBranch43_5
  · exact degreeUnionBranch43_6
  · exact degreeUnionBranch43_7
  · exact degreeUnionBranch43_8
  · exact degreeUnionBranch43_182
  · exact degreeUnionBranch43_351
  · exact degreeUnionBranch43_536
  · exact degreeUnionBranch43_611
  · exact degreeUnionBranch43_684
  · exact degreeUnionBranch43_732
  · exact degreeUnionBranch43_772
  · exact degreeUnionBranch43_813
  · exact degreeUnionBranch43_854
  · exact degreeUnionBranch43_895
  · exact degreeUnionBranch43_896
  · exact degreeUnionBranch43_897
  · exact degreeUnionBranch43_898
  · exact degreeUnionBranch43_899
  · exact degreeUnionBranch43_900

lemma degreeHalfCover43 : ∀ R ∈ degreeRegions43,
    R ∈ degreeHalfRegions43 ∨ (R.2,R.1) ∈ degreeHalfRegions43 := by decide +kernel

lemma degreeDiagramRegionsChecked43 : ∀ R ∈ degreeRegions43,
    ∀ μ : YoungDiagram, μ.card = 43 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP43 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck43 degreeHalfHeight43 degreeHalfWidth43
    degreeHalfCover43

end UniversalTensorSquare
end

end OAI
