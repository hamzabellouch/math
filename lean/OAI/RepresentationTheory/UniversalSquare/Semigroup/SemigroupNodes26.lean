import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes14
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes7
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes15

namespace OAI

/-! Semigroup Nodes 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10939 : RowSquare [7,6,2,2,2,2,1] [7,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4703

lemma sg10940 : RowSquare [7,6,2,2,2,2,1] [7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6324

lemma sg10941 : RowSquare [7,6,2,2,2,2,1] [7,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6325

lemma sg10942 : RowSquare [7,6,2,2,2,2,1] [7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg6326

lemma sg10943 : RowSquare [7,6,2,2,2,2,1] [7,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4702

lemma sg10944 : RowSquare [7,6,2,2,2,2,1] [7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4704

lemma sg10945 : RowSquare [7,6,2,2,2,2,1] [7,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6334

lemma sg10946 : RowSquare [7,6,2,2,2,2,1] [7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1149

lemma sg10947 : RowSquare [7,6,2,2,2,2,1] [7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg6335

lemma sg10948 : RowSquare [7,6,2,2,2,2,1] [7,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4705

lemma sg10949 : RowSquare [7,6,2,2,2,2,1] [7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1150

lemma sg10950 : RowSquare [7,6,2,2,2,2,1] [7,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg769 sg1633

lemma sg10951 : RowSquare [7,6,2,2,2,2,1] [7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1210 sg1146

lemma sg10952 : RowSquare [7,6,2,2,2,2,1] [7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6336

lemma sg10953 : RowSquare [7,6,2,2,2,2,1] [7,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg3861

lemma sg10954 : RowSquare [7,6,2,2,2,2,1] [7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg1148

lemma sg10955 : RowSquare [7,6,2,2,2,2,1] [7,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1203 sg1149

lemma sg10956 : RowSquare [7,6,2,2,2,2,1] [7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg3185

lemma sg10957 : RowSquare [7,6,2,2,2,2,1] [7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1203 sg1150

lemma sg10958 : RowSquare [7,6,2,2,2,2,1] [7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg770 sg1633

lemma sg10959 : RowSquare [7,6,2,2,2,2,1] [7,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4700

lemma sg10960 : RowSquare [7,6,2,2,2,2,1] [7,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4703

lemma sg10961 : RowSquare [7,6,2,2,2,2,1] [7,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4707

lemma sg10962 : RowSquare [7,6,2,2,2,2,1] [7,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6327

lemma sg10963 : RowSquare [7,6,2,2,2,2,1] [7,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1151

lemma sg10964 : RowSquare [7,6,2,2,2,2,1] [7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg6328

lemma sg10965 : RowSquare [7,6,2,2,2,2,1] [7,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg3863

lemma sg10966 : RowSquare [7,6,2,2,2,2,1] [7,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4708

lemma sg10967 : RowSquare [7,6,2,2,2,2,1] [7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1152

lemma sg10968 : RowSquare [7,6,2,2,2,2,1] [7,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1203 sg1151

lemma sg10969 : RowSquare [7,6,2,2,2,2,1] [7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1153

lemma sg10970 : RowSquare [7,6,2,2,2,2,1] [7,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1206 sg1150

lemma sg10971 : RowSquare [7,6,2,2,2,2,1] [7,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4706

lemma sg10972 : RowSquare [7,6,2,2,2,2,1] [7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1154

lemma sg10973 : RowSquare [7,6,2,2,2,2,1] [7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg3183

lemma sg10974 : RowSquare [7,6,2,2,2,2,1] [7,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5516

lemma sg10975 : RowSquare [7,6,2,2,2,2,1] [7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4707

lemma sg10976 : RowSquare [7,6,2,2,2,2,1] [7,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5522

lemma sg10977 : RowSquare [7,6,2,2,2,2,1] [7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1155

lemma sg10978 : RowSquare [7,6,2,2,2,2,1] [7,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1206 sg1151

lemma sg10979 : RowSquare [7,6,2,2,2,2,1] [7,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4708

lemma sg10980 : RowSquare [7,6,2,2,2,2,1] [7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1156

lemma sg10981 : RowSquare [7,6,2,2,2,2,1] [7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1157

lemma sg10982 : RowSquare [7,6,2,2,2,2,1] [7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5517

lemma sg10983 : RowSquare [7,6,2,2,2,2,1] [7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5518

lemma sg10984 : RowSquare [7,6,2,2,2,2,1] [7,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5523

lemma sg10985 : RowSquare [7,6,2,2,2,2,1] [7,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg3184

lemma sg10986 : RowSquare [7,6,2,2,2,2,1] [8,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg6318

lemma sg10987 : RowSquare [7,6,2,2,2,2,1] [8,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6329

lemma sg10988 : RowSquare [7,6,2,2,2,2,1] [8,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6337

lemma sg10989 : RowSquare [7,6,2,2,2,2,1] [8,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4709

lemma sg10990 : RowSquare [7,6,2,2,2,2,1] [8,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg6319

lemma sg10991 : RowSquare [7,6,2,2,2,2,1] [8,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg6320

lemma sg10992 : RowSquare [7,6,2,2,2,2,1] [8,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg6321

lemma sg10993 : RowSquare [7,6,2,2,2,2,1] [8,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg6322

lemma sg10994 : RowSquare [7,6,2,2,2,2,1] [8,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5519

lemma sg10995 : RowSquare [7,6,2,2,2,2,1] [8,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4709

lemma sg10996 : RowSquare [7,6,2,2,2,2,1] [8,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4710

lemma sg10997 : RowSquare [7,6,2,2,2,2,1] [8,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6331

lemma sg10998 : RowSquare [7,6,2,2,2,2,1] [8,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6332

lemma sg10999 : RowSquare [7,6,2,2,2,2,1] [8,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg6333

lemma sg11000 : RowSquare [7,6,2,2,2,2,1] [8,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4702

lemma sg11001 : RowSquare [7,6,2,2,2,2,1] [8,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4711

lemma sg11002 : RowSquare [7,6,2,2,2,2,1] [8,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6338

lemma sg11003 : RowSquare [7,6,2,2,2,2,1] [8,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg1149

lemma sg11004 : RowSquare [7,6,2,2,2,2,1] [8,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg3862

lemma sg11005 : RowSquare [7,6,2,2,2,2,1] [8,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg1150

lemma sg11006 : RowSquare [7,6,2,2,2,2,1] [8,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4701

lemma sg11007 : RowSquare [7,6,2,2,2,2,1] [8,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4710

lemma sg11008 : RowSquare [7,6,2,2,2,2,1] [8,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg3863

lemma sg11009 : RowSquare [7,6,2,2,2,2,1] [8,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5520

lemma sg11010 : RowSquare [7,6,2,2,2,2,1] [8,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1158

lemma sg11011 : RowSquare [7,6,2,2,2,2,1] [8,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4711

lemma sg11012 : RowSquare [7,6,2,2,2,2,1] [8,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4713

lemma sg11013 : RowSquare [7,6,2,2,2,2,1] [8,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1159

lemma sg11014 : RowSquare [7,6,2,2,2,2,1] [8,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1160

lemma sg11015 : RowSquare [7,6,2,2,2,2,1] [8,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg2592

lemma sg11016 : RowSquare [7,6,2,2,2,2,1] [8,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4703

lemma sg11017 : RowSquare [7,6,2,2,2,2,1] [8,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4712

lemma sg11018 : RowSquare [7,6,2,2,2,2,1] [8,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4714

lemma sg11019 : RowSquare [7,6,2,2,2,2,1] [8,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg1161

lemma sg11020 : RowSquare [7,6,2,2,2,2,1] [8,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg2593

lemma sg11021 : RowSquare [7,6,2,2,2,2,1] [8,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4707

lemma sg11022 : RowSquare [7,6,2,2,2,2,1] [8,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg240 sg2593

lemma sg11023 : RowSquare [7,6,2,2,2,2,1] [8,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg2593

lemma sg11024 : RowSquare [7,6,2,2,2,2,1] [9,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5515

lemma sg11025 : RowSquare [7,6,2,2,2,2,1] [9,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6337

lemma sg11026 : RowSquare [7,6,2,2,2,2,1] [9,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4709

lemma sg11027 : RowSquare [7,6,2,2,2,2,1] [9,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4715

lemma sg11028 : RowSquare [7,6,2,2,2,2,1] [9,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg6331

lemma sg11029 : RowSquare [7,6,2,2,2,2,1] [9,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg6332

lemma sg11030 : RowSquare [7,6,2,2,2,2,1] [9,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4709

lemma sg11031 : RowSquare [7,6,2,2,2,2,1] [9,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4715

lemma sg11032 : RowSquare [7,6,2,2,2,2,1] [9,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg4716

lemma sg11033 : RowSquare [7,6,2,2,2,2,1] [9,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg6338

lemma sg11034 : RowSquare [7,6,2,2,2,2,1] [9,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg3864

lemma sg11035 : RowSquare [7,6,2,2,2,2,1] [9,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg2592

lemma sg11036 : RowSquare [7,6,2,2,2,2,1] [9,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4710

lemma sg11037 : RowSquare [7,6,2,2,2,2,1] [9,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4716

lemma sg11038 : RowSquare [7,6,2,2,2,2,1] [9,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg2593

lemma sg11039 : RowSquare [7,6,2,2,2,2,1] [9,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg85 sg3863

lemma sg11040 : RowSquare [7,6,2,2,2,2,1] [10,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5519

lemma sg11041 : RowSquare [7,6,2,2,2,2,1] [10,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg4709

lemma sg11042 : RowSquare [7,6,2,2,2,2,1] [10,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg4715

lemma sg11043 : RowSquare [7,6,2,2,2,2,1] [10,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg3864

lemma sg11044 : RowSquare [7,6,2,2,2,2,1] [10,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg4715

lemma sg11045 : RowSquare [7,6,2,2,2,2,1] [10,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg4717

lemma sg11046 : RowSquare [7,6,2,2,2,2,1] [11,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg4709

lemma sg11047 : RowSquare [7,6,2,2,2,2,1] [11,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg4715

lemma sg11048 : RowSquare [7,7,1,1,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5551

lemma sg11049 : RowSquare [7,7,1,1,1,1,1,1,1,1] [5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg13 sg5552

lemma sg11050 : RowSquare [8,3,2,2,2,2,2,1] [5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg3995

lemma sg11051 : RowSquare [8,4,3,2,2,2,1] [4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg287 sg2546

lemma sg11052 : RowSquare [8,6,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg6396

lemma sg11053 : RowSquare [8,6,1,1,1,1,1,1,1,1] [6,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg110 sg3521

lemma sg11054 : RowSquare [8,6,1,1,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg111 sg3521

lemma sg11055 : RowSquare [8,6,1,1,1,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg112 sg3521

lemma sg11056 : RowSquare [9,3,2,2,2,2,1,1] [4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg74 sg3967

lemma sg11057 : RowSquare [9,3,2,2,2,2,1,1] [5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg3968

lemma sg11058 : RowSquare [9,3,2,2,2,2,2] [6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg165 sg3213

lemma sg11059 : RowSquare [9,7,3,2,1] [4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg878 sg1688

lemma sg11060 : RowSquare [10,3,2,2,2,2,1] [5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg3870

lemma sg11061 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4] := by
  exact rowSquare_join (by decide) sg1539 sg1978

lemma sg11062 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg1455 sg2008

lemma sg11063 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1540 sg1978

lemma sg11064 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1532 sg1993

lemma sg11065 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1541 sg1978

lemma sg11066 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5] := by
  exact rowSquare_join (by decide) sg1562 sg1926

lemma sg11067 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1455 sg2009

lemma sg11068 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1540 sg1980

lemma sg11069 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2] := by
  exact rowSquare_join (by decide) sg1532 sg1994

lemma sg11070 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,1] := by
  exact rowSquare_join (by decide) sg1541 sg1980

lemma sg11071 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg1540 sg1981

lemma sg11072 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,2] := by
  exact rowSquare_join (by decide) sg1532 sg1995

lemma sg11073 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,1] := by
  exact rowSquare_join (by decide) sg1533 sg1993

lemma sg11074 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4] := by
  exact rowSquare_join (by decide) sg1539 sg1987

lemma sg11075 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3] := by
  exact rowSquare_join (by decide) sg1539 sg1988

lemma sg11076 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1455 sg2010

lemma sg11077 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1542 sg1980

lemma sg11078 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2] := by
  exact rowSquare_join (by decide) sg1532 sg1996

lemma sg11079 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4] := by
  exact rowSquare_join (by decide) sg1544 sg1980

lemma sg11080 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1455 sg2011

lemma sg11081 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1572 sg1915

lemma sg11082 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2] := by
  exact rowSquare_join (by decide) sg1545 sg1979

lemma sg11083 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,1] := by
  exact rowSquare_join (by decide) sg1533 sg1996

lemma sg11084 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3] := by
  exact rowSquare_join (by decide) sg1539 sg1991

lemma sg11085 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1540 sg1983

lemma sg11086 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1455 sg2012

lemma sg11087 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1461 sg2002

lemma sg11088 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1460 sg2003

lemma sg11089 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1461 sg2003

lemma sg11090 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1540 sg1985

lemma sg11091 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1455 sg2013

lemma sg11092 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3] := by
  exact rowSquare_join (by decide) sg1461 sg2004

lemma sg11093 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [9,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1542 sg1985

lemma sg11094 : RowSquare [3,3,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg1532 sg1979

lemma sg11095 : RowSquare [3,3,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg1532 sg1980

lemma sg11096 : RowSquare [3,3,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,5] := by
  exact rowSquare_join (by decide) sg693 sg3152

lemma sg11097 : RowSquare [3,3,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3] := by
  exact rowSquare_join (by decide) sg1061 sg2479

lemma sg11098 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1517 sg1977

lemma sg11099 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg1519 sg1977

lemma sg11100 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1517 sg1979

lemma sg11101 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1517 sg1980

lemma sg11102 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1518 sg1979

lemma sg11103 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg1519 sg1979

lemma sg11104 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1518 sg1980

lemma sg11105 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg1519 sg1980

lemma sg11106 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg1979

lemma sg11107 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg2479

lemma sg11108 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg2003

lemma sg11109 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg2003

lemma sg11110 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1517 sg1985

lemma sg11111 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1524 sg1980

lemma sg11112 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg2004

lemma sg11113 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1518 sg1985

lemma sg11114 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1542 sg1956

lemma sg11115 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg2005

lemma sg11116 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1521 sg1983

lemma sg11117 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg2005

lemma sg11118 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1518 sg1987

lemma sg11119 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1519 sg1987

lemma sg11120 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1520 sg1985

lemma sg11121 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg2006

lemma sg11122 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1517 sg1989

lemma sg11123 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1521 sg1985

lemma sg11124 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg2006

lemma sg11125 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1518 sg1989

lemma sg11126 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,3] := by
  exact rowSquare_join (by decide) sg1519 sg1989

lemma sg11127 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg2007

lemma sg11128 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg2007

lemma sg11129 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1521 sg1986

lemma sg11130 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1518 sg1990

lemma sg11131 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,3,2] := by
  exact rowSquare_join (by decide) sg1519 sg1990

lemma sg11132 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,1] := by
  exact rowSquare_join (by decide) sg1541 sg1963

lemma sg11133 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1566 sg1903

lemma sg11134 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg1989

lemma sg11135 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1542 sg1961

lemma sg11136 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg1991

lemma sg11137 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1545 sg1961

lemma sg11138 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1520 sg1992

lemma sg11139 : RowSquare [4,3,2,2,2,2,2,2,2,1,1] [5,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg2364

lemma sg11140 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1517 sg1954

lemma sg11141 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1517 sg1955

lemma sg11142 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1517 sg1956

lemma sg11143 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1517 sg1957

lemma sg11144 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1520 sg1955

lemma sg11145 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1517 sg1958

lemma sg11146 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1520 sg1957

lemma sg11147 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1517 sg1961

lemma sg11148 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1520 sg1961

lemma sg11149 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg1963

lemma sg11150 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1902

lemma sg11151 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1416 sg1903

lemma sg11152 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg1908

lemma sg11153 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg1908

lemma sg11154 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1524 sg1811

lemma sg11155 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1416 sg1909

lemma sg11156 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [6,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1418 sg1902

lemma sg11157 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1418 sg1903

lemma sg11158 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [6,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1520 sg1814

lemma sg11159 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [6,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1520 sg1815

lemma sg11160 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [6,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg1913

lemma sg11161 : RowSquare [4,4,2,2,2,2,1,1,1,1,1,1,1] [6,6,6,5] := by
  exact rowSquare_join (by decide) sg1523 sg1819

lemma sg11162 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1032 sg2311

lemma sg11163 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1038 sg2311

lemma sg11164 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg2316

lemma sg11165 : RowSquare [4,4,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg3637

lemma sg11166 : RowSquare [5,3,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,5] := by
  exact rowSquare_join (by decide) sg390 sg3630

lemma sg11167 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1416 sg1874

lemma sg11168 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg2288

lemma sg11169 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg2288

lemma sg11170 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1498 sg1811

lemma sg11171 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1416 sg1875

lemma sg11172 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg1875

lemma sg11173 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1419 sg1874

lemma sg11174 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1420 sg1874

lemma sg11175 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1421 sg1874

lemma sg11176 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg2337

lemma sg11177 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg958 sg2370

lemma sg11178 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1422 sg1874

lemma sg11179 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg2291

lemma sg11180 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg2291

lemma sg11181 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1423 sg1874

lemma sg11182 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1424 sg1874

lemma sg11183 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1040 sg2288

lemma sg11184 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1425 sg1874

lemma sg11185 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1426 sg1874

lemma sg11186 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg2297

lemma sg11187 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1033 sg2297

lemma sg11188 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1498 sg1812

lemma sg11189 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1813

lemma sg11190 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1498 sg1814

lemma sg11191 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1816

lemma sg11192 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1421 sg1875

lemma sg11193 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1819

lemma sg11194 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1422 sg1875

lemma sg11195 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1435 sg1874

lemma sg11196 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1040 sg2291

lemma sg11197 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1436 sg1874

lemma sg11198 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg1040 sg2297

lemma sg11199 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg1522 sg1780

lemma sg11200 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg1522 sg1782

lemma sg11201 : RowSquare [5,4,2,2,2,1,1,1,1,1,1,1,1] [6,6,6,5] := by
  exact rowSquare_join (by decide) sg1523 sg1782

lemma sg11202 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1498 sg1944

lemma sg11203 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1498 sg1945

lemma sg11204 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1946

lemma sg11205 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1947

lemma sg11206 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1948

lemma sg11207 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1499 sg1945

lemma sg11208 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1499 sg1946

lemma sg11209 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1947

lemma sg11210 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1948

lemma sg11211 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1500 sg1946

lemma sg11212 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1500 sg1947

lemma sg11213 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1500 sg1948

lemma sg11214 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1501 sg1947

lemma sg11215 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1501 sg1948

lemma sg11216 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1502 sg1948

lemma sg11217 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1498 sg1949

lemma sg11218 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1950

lemma sg11219 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1499 sg1949

lemma sg11220 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1503 sg1946

lemma sg11221 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1503 sg1947

lemma sg11222 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1503 sg1948

lemma sg11223 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1500 sg1950

lemma sg11224 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1504 sg1947

lemma sg11225 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1504 sg1948

lemma sg11226 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1500 sg1951

lemma sg11227 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1501 sg1951

lemma sg11228 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1507 sg1948

lemma sg11229 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1500 sg1952

lemma sg11230 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1500 sg1953

lemma sg11231 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1501 sg1952

lemma sg11232 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1502 sg1952

lemma sg11233 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1501 sg1953

lemma sg11234 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1502 sg1953

lemma sg11235 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1503 sg1949

lemma sg11236 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1504 sg1950

lemma sg11237 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1523 sg1754

lemma sg11238 : RowSquare [6,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg676 sg2626

lemma sg11239 : RowSquare [6,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg889 sg2310

lemma sg11240 : RowSquare [6,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg889 sg2311

lemma sg11241 : RowSquare [6,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg2310

lemma sg11242 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1754

lemma sg11243 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1757

lemma sg11244 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1782

lemma sg11245 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg891 sg2288

lemma sg11246 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg2288

lemma sg11247 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1782

lemma sg11248 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1782

lemma sg11249 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg6563

lemma sg11250 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1379 sg1756

lemma sg11251 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg4 sg6566

lemma sg11252 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg4 sg6568

lemma sg11253 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1782

lemma sg11254 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg892 sg2297

lemma sg11255 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1327 sg1872

lemma sg11256 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1327 sg1754

lemma sg11257 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1754

lemma sg11258 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1754

lemma sg11259 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1754

lemma sg11260 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg1754

lemma sg11261 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1333 sg1754

lemma sg11262 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1334 sg1754

lemma sg11263 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1335 sg1754

lemma sg11264 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1328 sg1756

lemma sg11265 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1336 sg1754

lemma sg11266 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1757

lemma sg11267 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1337 sg1754

lemma sg11268 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1758

lemma sg11269 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1338 sg1754

lemma sg11270 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1329 sg1755

lemma sg11271 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1339 sg1754

lemma sg11272 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1329 sg1756

lemma sg11273 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1340 sg1754

lemma sg11274 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1329 sg1757

lemma sg11275 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg1755

lemma sg11276 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1758

lemma sg11277 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1766

lemma sg11278 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1330 sg1756

lemma sg11279 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1767

lemma sg11280 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1756

lemma sg11281 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1330 sg1757

lemma sg11282 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg1756

lemma sg11283 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1757

lemma sg11284 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg1757

lemma sg11285 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1758

lemma sg11286 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1758

lemma sg11287 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1341 sg1754

lemma sg11288 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1342 sg1754

lemma sg11289 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1343 sg1754

lemma sg11290 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1344 sg1754

lemma sg11291 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1333 sg1757

lemma sg11292 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1333 sg1758

lemma sg11293 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1345 sg1754

lemma sg11294 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1763

lemma sg11295 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1346 sg1754

lemma sg11296 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1764

lemma sg11297 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1347 sg1754

lemma sg11298 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1765

lemma sg11299 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1334 sg1757

lemma sg11300 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1337 sg1755

lemma sg11301 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1334 sg1758

lemma sg11302 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1768

lemma sg11303 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1766

lemma sg11304 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1335 sg1756

lemma sg11305 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1769

lemma sg11306 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1767

lemma sg11307 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1336 sg1756

lemma sg11308 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1337 sg1756

lemma sg11309 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1335 sg1758

lemma sg11310 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1336 sg1757

lemma sg11311 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1337 sg1757

lemma sg11312 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1337 sg1758

lemma sg11313 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1348 sg1754

lemma sg11314 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1770

lemma sg11315 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1338 sg1755

lemma sg11316 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1329 sg1763

lemma sg11317 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1349 sg1754

lemma sg11318 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1771

lemma sg11319 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1339 sg1755

lemma sg11320 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1764

lemma sg11321 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1330 sg1763

lemma sg11322 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1340 sg1755

lemma sg11323 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1765

lemma sg11324 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1763

lemma sg11325 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg1763

lemma sg11326 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1338 sg1758

lemma sg11327 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1772

lemma sg11328 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1766

lemma sg11329 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1330 sg1764

lemma sg11330 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1767

lemma sg11331 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1765

lemma sg11332 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1764

lemma sg11333 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg2277

lemma sg11334 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1764

lemma sg11335 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1340 sg1757

lemma sg11336 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1765

lemma sg11337 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1340 sg1758

lemma sg11338 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1765

end UniversalTensorSquare
end
end

end OAI
