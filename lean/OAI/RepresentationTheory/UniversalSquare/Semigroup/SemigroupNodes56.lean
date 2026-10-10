import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes47
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes49

namespace OAI

/-! Semigroup Nodes 56. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg22940 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6265 sg7483

lemma sg22941 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7139

lemma sg22942 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7079

lemma sg22943 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5510 sg8636

lemma sg22944 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg339 sg19573

lemma sg22945 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1306 sg14722

lemma sg22946 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1705 sg14411

lemma sg22947 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6266 sg7483

lemma sg22948 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7140

lemma sg22949 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7080

lemma sg22950 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7060

lemma sg22951 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6168 sg7529

lemma sg22952 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5512 sg8625

lemma sg22953 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1713 sg14408

lemma sg22954 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6267 sg7483

lemma sg22955 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7141

lemma sg22956 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7081

lemma sg22957 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7061

lemma sg22958 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6376 sg7057

lemma sg22959 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6152 sg7663

lemma sg22960 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7142

lemma sg22961 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7082

lemma sg22962 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7062

lemma sg22963 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6376 sg7058

lemma sg22964 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7189

lemma sg22965 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6340 sg7290

lemma sg22966 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7063

lemma sg22967 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6654

lemma sg22968 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7738

lemma sg22969 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6150 sg7677

lemma sg22970 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6370 sg7102

lemma sg22971 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6444 sg6789

lemma sg22972 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6365 sg7189

lemma sg22973 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6148 sg7738

lemma sg22974 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1315 sg14715

lemma sg22975 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2022 sg12942

lemma sg22976 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6268 sg7483

lemma sg22977 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7143

lemma sg22978 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7083

lemma sg22979 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7064

lemma sg22980 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6648

lemma sg22981 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6158 sg7595

lemma sg22982 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6269 sg7483

lemma sg22983 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7144

lemma sg22984 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6164 sg7581

lemma sg22985 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7065

lemma sg22986 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6168 sg7531

lemma sg22987 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7177

lemma sg22988 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6159 sg7595

lemma sg22989 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7084

lemma sg22990 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7066

lemma sg22991 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6649

lemma sg22992 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7190

lemma sg22993 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6367 sg7177

lemma sg22994 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6650

lemma sg22995 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7739

lemma sg22996 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7678

lemma sg22997 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6296 sg7433

lemma sg22998 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6427 sg6827

lemma sg22999 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7739

lemma sg23000 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7145

lemma sg23001 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7085

lemma sg23002 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7067

lemma sg23003 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6651

lemma sg23004 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7178

lemma sg23005 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6416 sg6828

lemma sg23006 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6285 sg7480

lemma sg23007 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6652

lemma sg23008 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7191

lemma sg23009 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7178

lemma sg23010 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6417 sg6828

lemma sg23011 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7740

lemma sg23012 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7679

lemma sg23013 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7740

lemma sg23014 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7191

lemma sg23015 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6653

lemma sg23016 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7741

lemma sg23017 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7179

lemma sg23018 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7741

lemma sg23019 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7680

lemma sg23020 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7192

lemma sg23021 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7434

lemma sg23022 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1307 sg14722

lemma sg23023 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1706 sg14411

lemma sg23024 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6270 sg7483

lemma sg23025 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7146

lemma sg23026 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7086

lemma sg23027 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3850 sg11506

lemma sg23028 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5365 sg8712

lemma sg23029 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4729 sg10578

lemma sg23030 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1308 sg14722

lemma sg23031 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2022 sg12943

lemma sg23032 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6271 sg7483

lemma sg23033 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7147

lemma sg23034 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7087

lemma sg23035 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7068

lemma sg23036 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6376 sg7060

lemma sg23037 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6153 sg7663

lemma sg23038 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6272 sg7483

lemma sg23039 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7148

lemma sg23040 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7088

lemma sg23041 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7069

lemma sg23042 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6376 sg7061

lemma sg23043 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7181

lemma sg23044 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6341 sg7290

lemma sg23045 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7089

lemma sg23046 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7070

lemma sg23047 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6655

lemma sg23048 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7193

lemma sg23049 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6367 sg7181

lemma sg23050 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6656

lemma sg23051 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7742

lemma sg23052 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7681

lemma sg23053 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6296 sg7435

lemma sg23054 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6430 sg6827

lemma sg23055 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7742

lemma sg23056 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1708 sg14411

lemma sg23057 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6273 sg7483

lemma sg23058 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7149

lemma sg23059 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7090

lemma sg23060 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7071

lemma sg23061 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6376 sg7064

lemma sg23062 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6368 sg7177

lemma sg23063 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6342 sg7290

lemma sg23064 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7150

lemma sg23065 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7091

lemma sg23066 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7072

lemma sg23067 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6657

lemma sg23068 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7182

lemma sg23069 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6406 sg6857

lemma sg23070 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7073

lemma sg23071 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6658

lemma sg23072 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7194

lemma sg23073 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7182

lemma sg23074 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6298 sg7433

lemma sg23075 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7743

lemma sg23076 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7682

lemma sg23077 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7743

lemma sg23078 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7194

lemma sg23079 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7092

lemma sg23080 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7074

lemma sg23081 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6659

lemma sg23082 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7183

lemma sg23083 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6406 sg6858

lemma sg23084 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6421 sg6828

lemma sg23085 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6660

lemma sg23086 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7744

lemma sg23087 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7183

lemma sg23088 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7744

lemma sg23089 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7683

lemma sg23090 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7195

lemma sg23091 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7196

lemma sg23092 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7684

lemma sg23093 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7196

lemma sg23094 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7436

lemma sg23095 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6274 sg7483

lemma sg23096 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7151

lemma sg23097 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7093

lemma sg23098 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5900 sg7860

lemma sg23099 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6212 sg7490

lemma sg23100 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6415 sg6833

lemma sg23101 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6408 sg6857

lemma sg23102 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7094

lemma sg23103 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7075

lemma sg23104 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6483 sg6639

lemma sg23105 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7185

lemma sg23106 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6416 sg6833

lemma sg23107 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6299 sg7433

lemma sg23108 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6483 sg6640

lemma sg23109 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7745

lemma sg23110 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7185

lemma sg23111 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7745

lemma sg23112 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7685

lemma sg23113 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7197

lemma sg23114 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7076

lemma sg23115 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6483 sg6641

lemma sg23116 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7746

lemma sg23117 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6416 sg6834

lemma sg23118 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7746

lemma sg23119 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7198

lemma sg23120 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7686

lemma sg23121 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7198

lemma sg23122 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7437

lemma sg23123 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7187

lemma sg23124 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7438

lemma sg23125 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6483 sg6642

lemma sg23126 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7199

lemma sg23127 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7687

lemma sg23128 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7199

lemma sg23129 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7188

lemma sg23130 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7439

lemma sg23131 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6304 sg7373

lemma sg23132 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1316 sg14717

lemma sg23133 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2023 sg12943

lemma sg23134 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1817 sg14307

lemma sg23135 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7152

lemma sg23136 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3796 sg11537

lemma sg23137 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6284 sg7482

lemma sg23138 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5296 sg8789

lemma sg23139 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6160 sg7598

lemma sg23140 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1718 sg14407

lemma sg23141 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1818 sg14307

lemma sg23142 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7153

lemma sg23143 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7095

lemma sg23144 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5909 sg7859

lemma sg23145 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6376 sg7068

lemma sg23146 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6368 sg7181

lemma sg23147 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6161 sg7598

lemma sg23148 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7154

lemma sg23149 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7096

lemma sg23150 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6214 sg7489

lemma sg23151 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6661

lemma sg23152 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6411 sg6840

lemma sg23153 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6406 sg6859

lemma sg23154 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6215 sg7489

lemma sg23155 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6662

lemma sg23156 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7200

lemma sg23157 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6412 sg6840

lemma sg23158 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6298 sg7435

lemma sg23159 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7747

lemma sg23160 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7688

lemma sg23161 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7747

lemma sg23162 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7200

lemma sg23163 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1819 sg14307

lemma sg23164 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7155

lemma sg23165 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7097

lemma sg23166 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6216 sg7489

lemma sg23167 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6663

lemma sg23168 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6368 sg7182

lemma sg23169 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6408 sg6859

lemma sg23170 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7098

lemma sg23171 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6217 sg7489

lemma sg23172 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6664

lemma sg23173 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6411 sg6841

lemma sg23174 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6406 sg6860

lemma sg23175 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6299 sg7435

lemma sg23176 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6665

lemma sg23177 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7748

lemma sg23178 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6412 sg6841

lemma sg23179 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7748

lemma sg23180 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7689

lemma sg23181 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7201

lemma sg23182 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6218 sg7489

lemma sg23183 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6666

lemma sg23184 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7749

lemma sg23185 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6406 sg6861

lemma sg23186 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7749

lemma sg23187 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7202

lemma sg23188 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7690

lemma sg23189 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7202

lemma sg23190 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6842

lemma sg23191 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6412 sg6843

lemma sg23192 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6843

lemma sg23193 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7156

lemma sg23194 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6374 sg7099

lemma sg23195 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6219 sg7489

lemma sg23196 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6667

lemma sg23197 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6368 sg7185

lemma sg23198 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6408 sg6860

lemma sg23199 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6424 sg6829

lemma sg23200 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6220 sg7489

lemma sg23201 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6668

lemma sg23202 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7750

lemma sg23203 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6406 sg6862

lemma sg23204 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7750

lemma sg23205 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7203

lemma sg23206 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7691

lemma sg23207 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7203

lemma sg23208 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6844

lemma sg23209 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6669

lemma sg23210 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7204

lemma sg23211 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7692

lemma sg23212 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7204

lemma sg23213 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6412 sg6845

lemma sg23214 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6845

lemma sg23215 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7438

lemma sg23216 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6411 sg6846

lemma sg23217 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6412 sg6846

lemma sg23218 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6846

lemma sg23219 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7439

lemma sg23220 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3795 sg11538

lemma sg23221 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6260 sg7484

lemma sg23222 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6219 sg7490

lemma sg23223 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7751

lemma sg23224 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6408 sg6862

lemma sg23225 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7751

lemma sg23226 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6220 sg7490

lemma sg23227 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7205

lemma sg23228 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7693

lemma sg23229 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7205

lemma sg23230 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6412 sg6847

lemma sg23231 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6847

lemma sg23232 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6411 sg6848

lemma sg23233 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6412 sg6848

lemma sg23234 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6848

lemma sg23235 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,6,6,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6479 sg6669

lemma sg23236 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1310 sg14718

lemma sg23237 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1710 sg14409

lemma sg23238 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6275 sg7483

lemma sg23239 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7157

lemma sg23240 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg294 sg20311

lemma sg23241 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg294 sg20312

lemma sg23242 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg294 sg20313

lemma sg23243 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1305 sg14723

lemma sg23244 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1704 sg14414

lemma sg23245 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6276 sg7483

lemma sg23246 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7158

lemma sg23247 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2173 sg12913

lemma sg23248 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg341 sg19570

lemma sg23249 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg341 sg19571

lemma sg23250 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1306 sg14723

lemma sg23251 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1705 sg14414

lemma sg23252 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6277 sg7483

lemma sg23253 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7159

lemma sg23254 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6221 sg7488

lemma sg23255 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7077

lemma sg23256 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5366 sg8710

lemma sg23257 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4730 sg10577

lemma sg23258 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1713 sg14409

lemma sg23259 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6278 sg7483

lemma sg23260 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3212 sg11746

lemma sg23261 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6222 sg7488

lemma sg23262 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6209 sg7491

lemma sg23263 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5366 sg8711

lemma sg23264 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6152 sg7676

lemma sg23265 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7160

lemma sg23266 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6223 sg7488

lemma sg23267 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7078

lemma sg23268 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6188 sg7503

lemma sg23269 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7206

lemma sg23270 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6340 sg7291

lemma sg23271 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6210 sg7491

lemma sg23272 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6654

lemma sg23273 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7752

lemma sg23274 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6150 sg7694

lemma sg23275 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6443 sg6790

lemma sg23276 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6445 sg6789

lemma sg23277 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6365 sg7206

lemma sg23278 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6148 sg7752

lemma sg23279 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1307 sg14723

lemma sg23280 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1706 sg14414

lemma sg23281 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6279 sg7483

lemma sg23282 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7161

lemma sg23283 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6224 sg7488

lemma sg23284 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7079

lemma sg23285 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5365 sg8713

lemma sg23286 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4729 sg10579

lemma sg23287 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1308 sg14723

lemma sg23288 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1707 sg14414

lemma sg23289 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6280 sg7483

lemma sg23290 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7162

lemma sg23291 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6225 sg7488

lemma sg23292 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7080

lemma sg23293 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6376 sg7077

lemma sg23294 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6153 sg7676

lemma sg23295 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6281 sg7483

lemma sg23296 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7163

lemma sg23297 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6226 sg7488

lemma sg23298 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7081

lemma sg23299 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6190 sg7503

lemma sg23300 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7189

lemma sg23301 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6341 sg7291

lemma sg23302 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6227 sg7488

lemma sg23303 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7082

lemma sg23304 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6670

lemma sg23305 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7207

lemma sg23306 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6367 sg7189

lemma sg23307 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6478 sg6671

lemma sg23308 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7753

lemma sg23309 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7695

lemma sg23310 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6296 sg7440

lemma sg23311 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6444 sg6790

lemma sg23312 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7753

lemma sg23313 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2024 sg12942

lemma sg23314 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6282 sg7483

lemma sg23315 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7164

lemma sg23316 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6228 sg7488

lemma sg23317 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7083

lemma sg23318 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6193 sg7503

lemma sg23319 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6415 sg6837

lemma sg23320 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6342 sg7291

lemma sg23321 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6369 sg7165

lemma sg23322 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6229 sg7488

lemma sg23323 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6213 sg7491

lemma sg23324 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6657

lemma sg23325 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7190

lemma sg23326 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6416 sg6837

lemma sg23327 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7084

lemma sg23328 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6658

lemma sg23329 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7208

lemma sg23330 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7190

lemma sg23331 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6417 sg6837

lemma sg23332 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7754

lemma sg23333 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7696

lemma sg23334 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7754

lemma sg23335 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7208

lemma sg23336 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6230 sg7488

lemma sg23337 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6375 sg7085

lemma sg23338 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6659

lemma sg23339 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7191

end UniversalTensorSquare
end
end

end OAI
