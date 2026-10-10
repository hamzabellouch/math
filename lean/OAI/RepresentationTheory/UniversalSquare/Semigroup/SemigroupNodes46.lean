import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes36

namespace OAI

/-! Semigroup Nodes 46. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18940 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg3382 sg4366

lemma sg18941 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3533 sg4277

lemma sg18942 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg3383 sg4366

lemma sg18943 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14145

lemma sg18944 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3533 sg4278

lemma sg18945 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3537 sg4267

lemma sg18946 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3534 sg4278

lemma sg18947 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4279

lemma sg18948 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg3534 sg4279

lemma sg18949 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14146

lemma sg18950 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3533 sg4280

lemma sg18951 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3381 sg4369

lemma sg18952 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3534 sg4280

lemma sg18953 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14147

lemma sg18954 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15059

lemma sg18955 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3536 sg4268

lemma sg18956 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg3534 sg4281

lemma sg18957 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4282

lemma sg18958 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg3663 sg4152

lemma sg18959 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg3534 sg4282

lemma sg18960 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg3537 sg4269

lemma sg18961 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14148

lemma sg18962 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14149

lemma sg18963 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15060

lemma sg18964 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15061

lemma sg18965 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3534 sg4283

lemma sg18966 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg4902

lemma sg18967 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4284

lemma sg18968 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg3534 sg4284

lemma sg18969 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15062

lemma sg18970 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4903

lemma sg18971 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3533 sg4285

lemma sg18972 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg3534 sg4285

lemma sg18973 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14150

lemma sg18974 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3533 sg4286

lemma sg18975 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3537 sg4270

lemma sg18976 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3534 sg4286

lemma sg18977 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14151

lemma sg18978 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4287

lemma sg18979 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2881 sg4888

lemma sg18980 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg3534 sg4287

lemma sg18981 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4288

lemma sg18982 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg3663 sg4153

lemma sg18983 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg3534 sg4288

lemma sg18984 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg3537 sg4271

lemma sg18985 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15063

lemma sg18986 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14152

lemma sg18987 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15064

lemma sg18988 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3350 sg4422

lemma sg18989 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg3534 sg4289

lemma sg18990 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14153

lemma sg18991 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14154

lemma sg18992 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4290

lemma sg18993 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15065

lemma sg18994 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3534 sg4290

lemma sg18995 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg3537 sg4272

lemma sg18996 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4291

lemma sg18997 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg3534 sg4291

lemma sg18998 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15066

lemma sg18999 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg3537 sg4273

lemma sg19000 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14155

lemma sg19001 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14156

lemma sg19002 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14157

lemma sg19003 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15067

lemma sg19004 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg3669 sg4151

lemma sg19005 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4904

lemma sg19006 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3663 sg4154

lemma sg19007 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg2710 sg4905

lemma sg19008 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15068

lemma sg19009 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14158

lemma sg19010 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14159

lemma sg19011 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15069

lemma sg19012 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15070

lemma sg19013 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3534 sg4292

lemma sg19014 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg4906

lemma sg19015 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14160

lemma sg19016 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14161

lemma sg19017 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14162

lemma sg19018 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15071

lemma sg19019 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15072

lemma sg19020 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg3537 sg4274

lemma sg19021 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3536 sg4275

lemma sg19022 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15073

lemma sg19023 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14163

lemma sg19024 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14164

lemma sg19025 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14165

lemma sg19026 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15074

lemma sg19027 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15075

lemma sg19028 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,2] := by
  exact rowSquare_join (by decide) sg2714 sg4903

lemma sg19029 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14166

lemma sg19030 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14167

lemma sg19031 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14168

lemma sg19032 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15076

lemma sg19033 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg1 sg15077

lemma sg19034 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14169

lemma sg19035 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2710 sg4907

lemma sg19036 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14127

lemma sg19037 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4293

lemma sg19038 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14170

lemma sg19039 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4294

lemma sg19040 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4295

lemma sg19041 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg3539 sg4271

lemma sg19042 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4908

lemma sg19043 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14171

lemma sg19044 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4296

lemma sg19045 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg4909

lemma sg19046 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14172

lemma sg19047 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14173

lemma sg19048 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg3347 sg4427

lemma sg19049 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4910

lemma sg19050 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3347 sg4428

lemma sg19051 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14174

lemma sg19052 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14175

lemma sg19053 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg2710 sg4911

lemma sg19054 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg2712 sg4905

lemma sg19055 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3381 sg4370

lemma sg19056 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14176

lemma sg19057 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4297

lemma sg19058 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3347 sg4429

lemma sg19059 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4912

lemma sg19060 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14177

lemma sg19061 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14178

lemma sg19062 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg3347 sg4430

lemma sg19063 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3539 sg4275

lemma sg19064 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg3540 sg4273

lemma sg19065 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14179

lemma sg19066 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14180

lemma sg19067 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14181

lemma sg19068 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,2] := by
  exact rowSquare_join (by decide) sg2714 sg4904

lemma sg19069 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,4,1] := by
  exact rowSquare_join (by decide) sg2714 sg4905

lemma sg19070 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14182

lemma sg19071 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14183

lemma sg19072 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14184

lemma sg19073 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg13 sg14185

lemma sg19074 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14128

lemma sg19075 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg4913

lemma sg19076 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14186

lemma sg19077 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg4914

lemma sg19078 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4914

lemma sg19079 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14188

lemma sg19080 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14189

lemma sg19081 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4915

lemma sg19082 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2625 sg4939

lemma sg19083 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2712 sg4908

lemma sg19084 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14129

lemma sg19085 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14190

lemma sg19086 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14130

lemma sg19087 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14191

lemma sg19088 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14193

lemma sg19089 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14135

lemma sg19090 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14194

lemma sg19091 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14195

lemma sg19092 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg3537 sg4279

lemma sg19093 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg3537 sg4281

lemma sg19094 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15078

lemma sg19095 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg3537 sg4282

lemma sg19096 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15079

lemma sg19097 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg3537 sg4283

lemma sg19098 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15080

lemma sg19099 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg3537 sg4287

lemma sg19100 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15081

lemma sg19101 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg3537 sg4288

lemma sg19102 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg3537 sg4289

lemma sg19103 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15082

lemma sg19104 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg3537 sg4290

lemma sg19105 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15083

lemma sg19106 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14196

lemma sg19107 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15084

lemma sg19108 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15085

lemma sg19109 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg3388 sg4367

lemma sg19110 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15086

lemma sg19111 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3537 sg4292

lemma sg19112 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12469

lemma sg19113 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15087

lemma sg19114 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15088

lemma sg19115 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg1 sg15089

lemma sg19116 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12470

lemma sg19117 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12471

lemma sg19118 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15090

lemma sg19119 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg1 sg15091

lemma sg19120 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14197

lemma sg19121 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12472

lemma sg19122 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg84 sg12473

lemma sg19123 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,4] := by
  exact rowSquare_join (by decide) sg84 sg12474

lemma sg19124 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg3537 sg4293

lemma sg19125 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg3539 sg4287

lemma sg19126 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg3537 sg4294

lemma sg19127 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3537 sg4295

lemma sg19128 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15092

lemma sg19129 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3537 sg4296

lemma sg19130 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12477

lemma sg19131 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15093

lemma sg19132 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg401 sg11553

lemma sg19133 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15094

lemma sg19134 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg3540 sg4288

lemma sg19135 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12479

lemma sg19136 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12480

lemma sg19137 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15095

lemma sg19138 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1 sg15096

lemma sg19139 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12481

lemma sg19140 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15097

lemma sg19141 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg706 sg11058

lemma sg19142 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12482

lemma sg19143 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12483

lemma sg19144 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15098

lemma sg19145 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg1 sg15099

lemma sg19146 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14198

lemma sg19147 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12484

lemma sg19148 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,3,1] := by
  exact rowSquare_join (by decide) sg84 sg12485

lemma sg19149 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,4] := by
  exact rowSquare_join (by decide) sg84 sg12486

lemma sg19150 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14199

lemma sg19151 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14200

lemma sg19152 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,3] := by
  exact rowSquare_join (by decide) sg13 sg14201

lemma sg19153 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg4913

lemma sg19154 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3347 sg4433

lemma sg19155 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4914

lemma sg19156 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14202

lemma sg19157 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg3539 sg4294

lemma sg19158 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg402 sg11553

lemma sg19159 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3539 sg4295

lemma sg19160 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2715 sg4908

lemma sg19161 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14187

lemma sg19162 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14203

lemma sg19163 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4916

lemma sg19164 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2712 sg4913

lemma sg19165 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg424 sg11548

lemma sg19166 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12494

lemma sg19167 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14204

lemma sg19168 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14205

lemma sg19169 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14192

lemma sg19170 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2712 sg4914

lemma sg19171 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg228 sg12339

lemma sg19172 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14206

lemma sg19173 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14207

lemma sg19174 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14208

lemma sg19175 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2716 sg4908

lemma sg19176 : RowSquare [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg3537 sg4298

lemma sg19177 : RowSquare [7,7,2,2,2,2,2,2,2,2,1] [5,5,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg11799

lemma sg19178 : RowSquare [7,7,2,2,2,2,2,2,2,2,1] [5,5,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg210 sg11800

lemma sg19179 : RowSquare [7,7,2,2,2,2,2,2,2,2,1] [5,5,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg210 sg11801

lemma sg19180 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2256 sg5750

lemma sg19181 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2622 sg4938

lemma sg19182 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2623 sg4938

lemma sg19183 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg3537 sg4173

lemma sg19184 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg3534 sg4178

lemma sg19185 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15103

lemma sg19186 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15104

lemma sg19187 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg3539 sg4172

lemma sg19188 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg3539 sg4173

lemma sg19189 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg3539 sg4174

lemma sg19190 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg3315 sg4423

lemma sg19191 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg3540 sg4170

lemma sg19192 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14220

lemma sg19193 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14221

lemma sg19194 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14223

lemma sg19195 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,3] := by
  exact rowSquare_join (by decide) sg3540 sg4173

lemma sg19196 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg3316 sg4423

lemma sg19197 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,2] := by
  exact rowSquare_join (by decide) sg3540 sg4174

lemma sg19198 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14224

lemma sg19199 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14225

lemma sg19200 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14226

lemma sg19201 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14227

lemma sg19202 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14228

lemma sg19203 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg13 sg14229

lemma sg19204 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg13 sg14230

lemma sg19205 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2712 sg4894

lemma sg19206 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14231

lemma sg19207 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14232

lemma sg19208 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14233

lemma sg19209 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14234

lemma sg19210 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14235

lemma sg19211 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14236

lemma sg19212 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14237

lemma sg19213 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14238

lemma sg19214 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2712 sg4895

lemma sg19215 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14239

lemma sg19216 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14240

lemma sg19217 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14241

lemma sg19218 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14242

lemma sg19219 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg13 sg14243

lemma sg19220 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg74 sg12722

lemma sg19221 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14244

lemma sg19222 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14245

lemma sg19223 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14246

lemma sg19224 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14247

lemma sg19225 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,4,1] := by
  exact rowSquare_join (by decide) sg13 sg14248

lemma sg19226 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg14249

lemma sg19227 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg83 sg12506

lemma sg19228 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg83 sg12507

lemma sg19229 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12508

lemma sg19230 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14250

lemma sg19231 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12509

lemma sg19232 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg2714 sg4895

lemma sg19233 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12510

lemma sg19234 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12511

lemma sg19235 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,2] := by
  exact rowSquare_join (by decide) sg83 sg12512

lemma sg19236 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,4,1] := by
  exact rowSquare_join (by decide) sg83 sg12513

lemma sg19237 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg83 sg12514

lemma sg19238 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14251

lemma sg19239 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14252

lemma sg19240 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14253

lemma sg19241 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,4] := by
  exact rowSquare_join (by decide) sg13 sg14254

lemma sg19242 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14255

lemma sg19243 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg13 sg14256

lemma sg19244 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3547 sg4166

lemma sg19245 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3547 sg4167

lemma sg19246 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg14212

lemma sg19247 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg3541 sg4168

lemma sg19248 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3548 sg4167

lemma sg19249 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3535 sg4175

lemma sg19250 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg3542 sg4168

lemma sg19251 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3533 sg4181

lemma sg19252 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15105

lemma sg19253 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg3534 sg4181

lemma sg19254 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg3536 sg4175

lemma sg19255 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3534 sg4182

lemma sg19256 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3314 sg4425

lemma sg19257 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14213

lemma sg19258 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg3543 sg4168

lemma sg19259 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3549 sg4167

lemma sg19260 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15106

lemma sg19261 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg3544 sg4168

lemma sg19262 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14257

lemma sg19263 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3538 sg4175

lemma sg19264 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg3663 sg4061

lemma sg19265 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15107

lemma sg19266 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15108

lemma sg19267 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg3314 sg4426

lemma sg19268 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3534 sg4183

lemma sg19269 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg3537 sg4176

lemma sg19270 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15109

lemma sg19271 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15110

lemma sg19272 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14258

lemma sg19273 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14259

lemma sg19274 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14260

lemma sg19275 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg15111

lemma sg19276 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15112

lemma sg19277 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15113

lemma sg19278 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15114

lemma sg19279 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3537 sg4177

lemma sg19280 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14261

lemma sg19281 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14262

lemma sg19282 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14263

lemma sg19283 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15115

lemma sg19284 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14264

lemma sg19285 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15116

lemma sg19286 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15117

lemma sg19287 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg3663 sg4062

lemma sg19288 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15118

lemma sg19289 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1 sg15119

lemma sg19290 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15120

lemma sg19291 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg3546 sg4168

lemma sg19292 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14214

lemma sg19293 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15121

lemma sg19294 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14265

lemma sg19295 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14266

lemma sg19296 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14267

lemma sg19297 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg15122

lemma sg19298 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15123

lemma sg19299 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15124

lemma sg19300 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15125

lemma sg19301 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3537 sg4180

lemma sg19302 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15126

lemma sg19303 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15127

lemma sg19304 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15128

lemma sg19305 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3314 sg4429

lemma sg19306 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12869

lemma sg19307 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14268

lemma sg19308 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14269

lemma sg19309 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14270

lemma sg19310 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15129

lemma sg19311 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15130

lemma sg19312 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15131

lemma sg19313 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14271

lemma sg19314 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14272

lemma sg19315 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14273

lemma sg19316 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14274

lemma sg19317 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14275

lemma sg19318 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14276

lemma sg19319 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1 sg15132

lemma sg19320 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15133

lemma sg19321 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1 sg15134

lemma sg19322 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14277

lemma sg19323 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12515

lemma sg19324 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15135

lemma sg19325 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11604

lemma sg19326 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12516

lemma sg19327 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12517

lemma sg19328 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12506

lemma sg19329 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11605

lemma sg19330 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12518

lemma sg19331 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11606

lemma sg19332 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg15136

lemma sg19333 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12873

lemma sg19334 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12507

lemma sg19335 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12874

lemma sg19336 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12508

lemma sg19337 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11607

lemma sg19338 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12509

lemma sg19339 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,2] := by
  exact rowSquare_join (by decide) sg165 sg11608

end UniversalTensorSquare
end
end

end OAI
