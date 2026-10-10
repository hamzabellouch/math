import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes5

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4919 : RowSquare [8,4,3,1,1] [3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg307 sg586

lemma sg4920 : RowSquare [8,4,3,1,1] [3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg306 sg587

lemma sg4921 : RowSquare [8,4,3,1,1] [3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg306 sg589

lemma sg4922 : RowSquare [8,4,3,1,1] [3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg310 sg586

lemma sg4923 : RowSquare [8,4,3,1,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1687

lemma sg4924 : RowSquare [8,4,3,1,1] [3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg1688

lemma sg4925 : RowSquare [8,4,3,1,1] [4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg307 sg588

lemma sg4926 : RowSquare [8,4,3,2] [3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg548

lemma sg4927 : RowSquare [8,4,3,2] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg178 sg854

lemma sg4928 : RowSquare [8,4,4,1] [3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg516

lemma sg4929 : RowSquare [8,6,2,1] [3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg849

lemma sg4931 : RowSquare [9,1,1,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg1136

lemma sg4932 : RowSquare [9,1,1,1,1,1,1,1,1] [2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg1620

lemma sg4933 : RowSquare [9,1,1,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2114

lemma sg4934 : RowSquare [9,2,2,2,1,1] [5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg518

lemma sg4935 : RowSquare [9,3,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2702

lemma sg4936 : RowSquare [9,3,1,1,1,1,1] [2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2251

lemma sg4937 : RowSquare [9,3,1,1,1,1,1] [3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2708

lemma sg4938 : RowSquare [9,3,1,1,1,1,1] [3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2256

lemma sg4939 : RowSquare [9,3,1,1,1,1,1] [4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2256

lemma sg4940 : RowSquare [9,3,1,1,1,1,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2713

lemma sg4941 : RowSquare [9,3,2,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1754

lemma sg4942 : RowSquare [9,3,2,1,1,1] [3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg1328

lemma sg4943 : RowSquare [9,3,2,1,1,1] [3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg1329

lemma sg4944 : RowSquare [9,3,2,1,1,1] [3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg77 sg1327

lemma sg4945 : RowSquare [9,3,2,1,1,1] [3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg1330

lemma sg4946 : RowSquare [9,3,2,1,1,1] [3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1757

lemma sg4947 : RowSquare [9,3,2,1,1,1] [3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg1331

lemma sg4948 : RowSquare [9,3,2,1,1,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1758

lemma sg4949 : RowSquare [9,3,2,1,1,1] [3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg74 sg1332

lemma sg4950 : RowSquare [9,3,2,1,1,1] [4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg75 sg1330

lemma sg4951 : RowSquare [9,3,2,1,1,1] [4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg1757

lemma sg4952 : RowSquare [9,3,2,1,1,1] [4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg75 sg1331

lemma sg4953 : RowSquare [9,3,2,1,1,1] [4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg76 sg1329

lemma sg4954 : RowSquare [9,3,2,1,1,1] [4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg1338

lemma sg4955 : RowSquare [9,3,2,1,1,1] [4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg194 sg890

lemma sg4956 : RowSquare [9,3,2,1,1,1] [4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg1339

lemma sg4957 : RowSquare [9,3,2,1,1,1] [4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg76 sg1331

lemma sg4958 : RowSquare [9,3,2,1,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg194 sg892

lemma sg4959 : RowSquare [9,3,2,1,1,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg77 sg1330

lemma sg4960 : RowSquare [9,3,2,1,1,1] [4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg77 sg1332

lemma sg4961 : RowSquare [9,3,2,1,1,1] [4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg195 sg891

lemma sg4962 : RowSquare [9,3,2,1,1,1] [4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg195 sg892

lemma sg4963 : RowSquare [9,3,2,1,1,1] [5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg89 sg1262

lemma sg4964 : RowSquare [9,3,2,2,1] [2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg910

lemma sg4965 : RowSquare [9,3,2,2,1] [2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg586

lemma sg4966 : RowSquare [9,3,2,2,1] [3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg587

lemma sg4967 : RowSquare [9,3,2,2,1] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg178 sg915

lemma sg4968 : RowSquare [9,3,2,2,1] [4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg179 sg915

lemma sg4969 : RowSquare [9,3,3,1,1] [3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg350 sg586

lemma sg4970 : RowSquare [9,3,3,1,1] [4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg350 sg588

lemma sg4971 : RowSquare [9,3,3,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg155 sg1001

lemma sg4972 : RowSquare [9,3,3,1,1] [4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg156 sg999

lemma sg4973 : RowSquare [9,3,3,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg350 sg590

lemma sg4974 : RowSquare [9,3,3,1,1] [5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg354 sg586

lemma sg4975 : RowSquare [9,3,3,1,1] [6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg354 sg588

lemma sg4976 : RowSquare [9,3,3,2] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg178 sg943

lemma sg4977 : RowSquare [9,3,3,2] [4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg179 sg943

lemma sg4978 : RowSquare [9,3,3,2] [4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg550

lemma sg4979 : RowSquare [9,3,3,2] [4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg371 sg551

lemma sg4980 : RowSquare [9,3,3,2] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg180 sg943

lemma sg4981 : RowSquare [9,4,1,1,1,1] [4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg1329

lemma sg4982 : RowSquare [9,4,1,1,1,1] [4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg1758

lemma sg4983 : RowSquare [9,4,1,1,1,1] [4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg1330

lemma sg4984 : RowSquare [9,4,1,1,1,1] [4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg1332

lemma sg4985 : RowSquare [9,4,1,1,1,1] [5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg40 sg1762

lemma sg4986 : RowSquare [9,4,2,1,1] [4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg534

lemma sg4987 : RowSquare [9,4,2,1,1] [4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg356 sg588

lemma sg4988 : RowSquare [9,4,2,1,1] [4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg535

lemma sg4989 : RowSquare [9,4,2,1,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg194 sg915

lemma sg4990 : RowSquare [9,4,3,1] [3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg636

lemma sg4991 : RowSquare [10,2,1,1,1,1,1] [5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg2263

lemma sg4992 : RowSquare [10,2,2,2,1] [3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg586

lemma sg4993 : RowSquare [10,2,2,2,1] [4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg179 sg1001

lemma sg4994 : RowSquare [10,2,2,2,1] [4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg589

lemma sg4995 : RowSquare [10,2,2,2,1] [4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg180 sg1001

lemma sg4996 : RowSquare [10,2,2,2,1] [4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg372 sg589

lemma sg4997 : RowSquare [10,3,2,1,1] [3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg586

lemma sg4998 : RowSquare [10,3,2,1,1] [4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg588

lemma sg4999 : RowSquare [10,3,2,1,1] [4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg195 sg999

lemma sg5000 : RowSquare [10,3,2,1,1] [4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg390 sg590

lemma sg5001 : RowSquare [10,3,2,1,1] [5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg586

lemma sg5002 : RowSquare [10,3,2,2] [3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg1032

lemma sg5003 : RowSquare [10,3,2,2] [3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1033

lemma sg5004 : RowSquare [10,3,2,2] [4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg179 sg1032

lemma sg5005 : RowSquare [10,3,3,1] [4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg179 sg1061

lemma sg5006 : RowSquare [10,3,3,1] [4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg1063

lemma sg5007 : RowSquare [10,3,3,1] [4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg636

lemma sg5008 : RowSquare [10,3,3,1] [4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1064

lemma sg5009 : RowSquare [10,3,3,1] [4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1065

lemma sg5010 : RowSquare [10,3,3,1] [4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg373 sg636

lemma sg5018 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg692 sg692

lemma sg5019 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg692 sg693

lemma sg5020 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,4] := by
  exact rowSquare_join (by decide) sg693 sg693

lemma sg5021 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,5,3,2,2] := by
  exact rowSquare_join (by decide) sg692 sg694

lemma sg5022 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,1] := by
  exact rowSquare_join (by decide) sg694 sg693

lemma sg5023 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,5,4,3] := by
  exact rowSquare_join (by decide) sg693 sg695

lemma sg5024 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,2] := by
  exact rowSquare_join (by decide) sg693 sg696

lemma sg5025 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg694 sg694

lemma sg5026 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [6,6,3,3] := by
  exact rowSquare_join (by decide) sg390 sg1109

lemma sg5027 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg643 sg708

lemma sg5028 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg697 sg693

lemma sg5029 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,2] := by
  exact rowSquare_join (by decide) sg644 sg708

lemma sg5030 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg697 sg694

lemma sg5031 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg643 sg709

lemma sg5032 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,4,3,2,2] := by
  exact rowSquare_join (by decide) sg692 sg698

lemma sg5033 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,1] := by
  exact rowSquare_join (by decide) sg644 sg709

lemma sg5034 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg391 sg1109

lemma sg5035 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,5,2,2,2] := by
  exact rowSquare_join (by decide) sg694 sg698

lemma sg5036 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg636 sg714

lemma sg5037 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,5,3,2,1] := by
  exact rowSquare_join (by decide) sg637 sg714

lemma sg5038 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,5,3,3] := by
  exact rowSquare_join (by decide) sg693 sg699

lemma sg5039 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg424 sg1063

lemma sg5040 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [8,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg697 sg697

lemma sg5041 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [8,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg645 sg708

lemma sg5042 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [8,3,3,2,2] := by
  exact rowSquare_join (by decide) sg692 sg702

lemma sg5043 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [8,3,3,3,1] := by
  exact rowSquare_join (by decide) sg644 sg711

lemma sg5044 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [8,4,2,2,2] := by
  exact rowSquare_join (by decide) sg694 sg702

lemma sg5045 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [8,7,1,1,1] := by
  exact rowSquare_join (by decide) sg694 sg703

lemma sg5046 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [9,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg576 sg716

lemma sg5047 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1] [9,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg576 sg717

lemma sg5048 : RowSquare [4,2,2,2,1,1,1,1,1,1,1,1] [6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg706

lemma sg5049 : RowSquare [4,2,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg422 sg1032

lemma sg5050 : RowSquare [4,2,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg422 sg1033

lemma sg5051 : RowSquare [4,2,2,2,1,1,1,1,1,1,1,1] [6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg424 sg1031

lemma sg5052 : RowSquare [4,2,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg424 sg1032

lemma sg5053 : RowSquare [4,2,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg424 sg1033

lemma sg5054 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg692

lemma sg5055 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg693

lemma sg5056 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg413 sg1032

lemma sg5057 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg413 sg1033

lemma sg5058 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg694

lemma sg5059 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg695

lemma sg5060 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg692

lemma sg5061 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg674 sg693

lemma sg5062 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,2] := by
  exact rowSquare_join (by decide) sg414 sg1033

lemma sg5063 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg696

lemma sg5064 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg415 sg1032

lemma sg5065 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg692 sg675

lemma sg5066 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg692 sg676

lemma sg5067 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,4] := by
  exact rowSquare_join (by decide) sg693 sg676

lemma sg5068 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg1109

lemma sg5069 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg694

lemma sg5070 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg1110

lemma sg5071 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg695

lemma sg5072 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,3,2,2] := by
  exact rowSquare_join (by decide) sg675 sg694

lemma sg5073 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,1] := by
  exact rowSquare_join (by decide) sg694 sg676

lemma sg5074 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg696

lemma sg5075 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg675 sg695

lemma sg5076 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,4,3] := by
  exact rowSquare_join (by decide) sg676 sg695

lemma sg5077 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg675 sg696

lemma sg5078 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,2] := by
  exact rowSquare_join (by decide) sg676 sg696

lemma sg5079 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1109

lemma sg5080 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1110

lemma sg5081 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg1109

lemma sg5082 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,3,3] := by
  exact rowSquare_join (by decide) sg373 sg1109

lemma sg5083 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg372 sg1110

lemma sg5084 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,2] := by
  exact rowSquare_join (by decide) sg373 sg1110

lemma sg5085 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg674 sg697

lemma sg5086 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg708

lemma sg5087 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg697 sg676

lemma sg5088 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,2] := by
  exact rowSquare_join (by decide) sg616 sg708

lemma sg5089 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg698

lemma sg5090 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg615 sg709

lemma sg5091 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,4,3,2,2] := by
  exact rowSquare_join (by decide) sg692 sg678

lemma sg5092 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,1] := by
  exact rowSquare_join (by decide) sg616 sg709

lemma sg5093 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg699

lemma sg5094 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,5,2,2,2] := by
  exact rowSquare_join (by decide) sg694 sg678

lemma sg5095 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg700

lemma sg5096 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,5,3,2,1] := by
  exact rowSquare_join (by decide) sg692 sg680

lemma sg5097 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,5,3,3] := by
  exact rowSquare_join (by decide) sg693 sg680

lemma sg5098 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1112

lemma sg5099 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg697 sg677

lemma sg5100 : RowSquare [4,3,2,1,1,1,1,1,1,1,1,1] [8,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg615 sg711

lemma sg5101 : RowSquare [4,3,2,2,1,1,1,1,1,1,1] [4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg389 sg1031

lemma sg5102 : RowSquare [4,3,2,2,1,1,1,1,1,1,1] [4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg1031

lemma sg5103 : RowSquare [4,3,2,2,1,1,1,1,1,1,1] [4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg389 sg1032

lemma sg5104 : RowSquare [4,3,2,2,1,1,1,1,1,1,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg389 sg1033

lemma sg5105 : RowSquare [4,3,2,2,1,1,1,1,1,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg390 sg1032

lemma sg5106 : RowSquare [4,3,2,2,1,1,1,1,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg390 sg1033

lemma sg5107 : RowSquare [4,3,2,2,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg692

lemma sg5108 : RowSquare [4,3,2,2,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg693

lemma sg5109 : RowSquare [4,3,2,2,2,2,2,1] [4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg561 sg579

lemma sg5110 : RowSquare [4,3,2,2,2,2,2,1] [5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg561 sg581

lemma sg5111 : RowSquare [4,3,2,2,2,2,2,1] [5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg366 sg849

lemma sg5112 : RowSquare [4,3,2,2,2,2,2,1] [5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg561 sg582

lemma sg5113 : RowSquare [4,3,2,2,2,2,2,1] [5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg849

lemma sg5114 : RowSquare [4,3,2,2,2,2,2,1] [5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg365 sg851

lemma sg5115 : RowSquare [4,3,2,2,2,2,2,1] [5,5,4,4] := by
  exact rowSquare_join (by decide) sg364 sg861

lemma sg5116 : RowSquare [4,3,2,2,2,2,2,1] [6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg368 sg849

lemma sg5117 : RowSquare [4,3,2,2,2,2,2,1] [6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg561 sg585

lemma sg5118 : RowSquare [4,3,2,2,2,2,2,1] [7,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg369 sg849

lemma sg5119 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1063

lemma sg5120 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1064

lemma sg5121 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg348 sg1032

lemma sg5122 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1065

lemma sg5123 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg389 sg941

lemma sg5124 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg636 sg615

lemma sg5125 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg941

lemma sg5126 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg389 sg943

lemma sg5127 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg637 sg616

lemma sg5128 : RowSquare [4,3,3,2,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg413 sg849

lemma sg5129 : RowSquare [4,3,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg576 sg673

lemma sg5130 : RowSquare [4,3,3,2,1,1,1,1,1,1] [5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1066

lemma sg5131 : RowSquare [4,3,3,2,1,1,1,1,1,1] [6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg231 sg1232

lemma sg5132 : RowSquare [4,3,3,2,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg1232

lemma sg5133 : RowSquare [4,3,3,2,1,1,1,1,1,1] [6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1067

lemma sg5134 : RowSquare [4,3,3,2,1,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg233 sg1232

lemma sg5135 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg673 sg673

lemma sg5136 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg674

lemma sg5137 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg675

lemma sg5138 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg676

lemma sg5139 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg674 sg674

lemma sg5140 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg675

lemma sg5141 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg674 sg676

lemma sg5142 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg675 sg675

lemma sg5143 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg675 sg676

lemma sg5144 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [6,4,4,4] := by
  exact rowSquare_join (by decide) sg676 sg676

lemma sg5145 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg677

lemma sg5146 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg678

lemma sg5147 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg674 sg677

lemma sg5148 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg679

lemma sg5149 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg677 sg675

lemma sg5150 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg677 sg676

lemma sg5151 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg680

lemma sg5152 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg678

lemma sg5153 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg681

lemma sg5154 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg679

lemma sg5155 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2] := by
  exact rowSquare_join (by decide) sg675 sg678

lemma sg5156 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,1] := by
  exact rowSquare_join (by decide) sg678 sg676

lemma sg5157 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,1] := by
  exact rowSquare_join (by decide) sg675 sg679

lemma sg5158 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,4,4,3] := by
  exact rowSquare_join (by decide) sg676 sg679

lemma sg5159 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg680

lemma sg5160 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg681

lemma sg5161 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,5,3,2,1] := by
  exact rowSquare_join (by decide) sg675 sg680

lemma sg5162 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,5,3,3] := by
  exact rowSquare_join (by decide) sg676 sg680

lemma sg5163 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,5,4,1,1] := by
  exact rowSquare_join (by decide) sg675 sg681

lemma sg5164 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [7,5,4,2] := by
  exact rowSquare_join (by decide) sg676 sg681

lemma sg5165 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg677 sg677

lemma sg5166 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg682

lemma sg5167 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg677 sg679

lemma sg5168 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2] := by
  exact rowSquare_join (by decide) sg675 sg682

lemma sg5169 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,1] := by
  exact rowSquare_join (by decide) sg682 sg676

lemma sg5170 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg683

lemma sg5171 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,2] := by
  exact rowSquare_join (by decide) sg678 sg678

lemma sg5172 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg684

lemma sg5173 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,1] := by
  exact rowSquare_join (by decide) sg675 sg683

lemma sg5174 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,4,3,3] := by
  exact rowSquare_join (by decide) sg676 sg683

lemma sg5175 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,4,4,2] := by
  exact rowSquare_join (by decide) sg676 sg684

lemma sg5176 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg685

lemma sg5177 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,5,2,2,1] := by
  exact rowSquare_join (by decide) sg678 sg680

lemma sg5178 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,5,3,1,1] := by
  exact rowSquare_join (by decide) sg675 sg685

lemma sg5179 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,5,3,2] := by
  exact rowSquare_join (by decide) sg676 sg685

lemma sg5180 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg686

lemma sg5181 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,6,2,2] := by
  exact rowSquare_join (by decide) sg676 sg686

lemma sg5182 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg677 sg682

lemma sg5183 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg687

lemma sg5184 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,3,2,2,2] := by
  exact rowSquare_join (by decide) sg678 sg682

lemma sg5185 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg677 sg684

lemma sg5186 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,3,3,2,1] := by
  exact rowSquare_join (by decide) sg675 sg687

lemma sg5187 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,3,3,3] := by
  exact rowSquare_join (by decide) sg676 sg687

lemma sg5188 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg688

lemma sg5189 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,4,3,2] := by
  exact rowSquare_join (by decide) sg676 sg688

lemma sg5190 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg689

lemma sg5191 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,5,2,2] := by
  exact rowSquare_join (by decide) sg676 sg689

lemma sg5192 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [9,7,1,1] := by
  exact rowSquare_join (by decide) sg680 sg686

lemma sg5193 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [10,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg677 sg687

lemma sg5194 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [10,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg690

lemma sg5195 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [10,3,3,2] := by
  exact rowSquare_join (by decide) sg676 sg690

lemma sg5196 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [10,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg691

lemma sg5197 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg1031

lemma sg5198 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg1032

lemma sg5199 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg370 sg1033

lemma sg5200 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg1520

lemma sg5201 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg1031

lemma sg5202 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg371 sg1032

lemma sg5203 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg371 sg1033

lemma sg5204 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg372 sg1031

lemma sg5205 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1031

lemma sg5206 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg1032

lemma sg5207 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg372 sg1033

lemma sg5208 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1032

lemma sg5209 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg373 sg1033

lemma sg5210 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg673

lemma sg5211 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg674

lemma sg5212 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg673

lemma sg5213 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg675

lemma sg5214 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg615

lemma sg5215 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg676

lemma sg5216 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg616

lemma sg5217 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg374 sg1032

lemma sg5218 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg374 sg1033

lemma sg5219 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg614 sg674

lemma sg5220 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg675

lemma sg5221 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg674

lemma sg5222 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg614 sg676

lemma sg5223 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg674 sg616

lemma sg5224 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg375 sg1033

lemma sg5225 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg1041

lemma sg5226 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg675

lemma sg5227 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg615 sg676

lemma sg5228 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg1527

lemma sg5229 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg1038

lemma sg5230 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg377 sg1031

lemma sg5231 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg1039

lemma sg5232 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1040

lemma sg5233 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg378 sg1031

lemma sg5234 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1041

lemma sg5235 : RowSquare [4,4,2,1,1,1,1,1,1,1,1] [5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg372 sg1039

lemma sg5236 : RowSquare [4,4,2,2,1,1,1,1,1,1] [3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg1031

lemma sg5237 : RowSquare [4,4,2,2,1,1,1,1,1,1] [3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1032

lemma sg5238 : RowSquare [4,4,2,2,1,1,1,1,1,1] [3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg1417

lemma sg5239 : RowSquare [4,4,2,2,1,1,1,1,1,1] [3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1033

lemma sg5240 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg613 sg613

lemma sg5241 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg615

lemma sg5242 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1038

lemma sg5243 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg614

lemma sg5244 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1039

lemma sg5245 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg614 sg615

lemma sg5246 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1040

lemma sg5247 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg616

lemma sg5248 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg371 sg960

lemma sg5249 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg371 sg961

lemma sg5250 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1041

lemma sg5251 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg372 sg959

lemma sg5252 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg615

lemma sg5253 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg959

lemma sg5254 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg615 sg616

lemma sg5255 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg372 sg961

lemma sg5256 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg373 sg960

lemma sg5257 : RowSquare [4,4,2,2,1,1,1,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg616 sg616

lemma sg5258 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg617

lemma sg5259 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg620

lemma sg5260 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg375 sg961

lemma sg5261 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg623

lemma sg5262 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg621

lemma sg5263 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg964

lemma sg5264 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1049

lemma sg5265 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg616 sg621

lemma sg5266 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg614 sg623

lemma sg5267 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,4,4] := by
  exact rowSquare_join (by decide) sg373 sg965

lemma sg5268 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg615 sg623

lemma sg5269 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg616 sg623

lemma sg5270 : RowSquare [4,4,2,2,1,1,1,1,1,1] [5,5,5,3] := by
  exact rowSquare_join (by decide) sg373 sg966

lemma sg5271 : RowSquare [4,4,2,2,1,1,1,1,1,1] [6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg624

lemma sg5272 : RowSquare [4,4,2,2,1,1,1,1,1,1] [6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg673 sg565

lemma sg5273 : RowSquare [4,4,2,2,1,1,1,1,1,1] [6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg625

lemma sg5274 : RowSquare [4,4,2,2,1,1,1,1,1,1] [6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg379 sg961

lemma sg5275 : RowSquare [4,4,2,2,1,1,1,1,1,1] [6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg626

lemma sg5276 : RowSquare [4,4,2,2,1,1,1,1,1,1] [6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg627

lemma sg5277 : RowSquare [4,4,2,2,1,1,1,1,1,1] [6,6,6] := by
  exact rowSquare_join (by decide) sg623 sg623

lemma sg5278 : RowSquare [4,4,2,2,2,2,1,1] [3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg1650

lemma sg5279 : RowSquare [4,4,2,2,2,2,1,1] [3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg878

lemma sg5280 : RowSquare [4,4,2,2,2,2,1,1] [4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg1650

lemma sg5281 : RowSquare [4,4,2,2,2,2,1,1] [4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg561 sg561

lemma sg5282 : RowSquare [4,4,2,2,2,2,1,1] [4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg1650

lemma sg5283 : RowSquare [4,4,2,2,2,2,1,1] [4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg1651

lemma sg5284 : RowSquare [4,4,2,2,2,2,1,1] [4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg1652

lemma sg5285 : RowSquare [4,4,2,2,2,2,1,1] [4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg885

lemma sg5286 : RowSquare [4,4,2,2,2,2,1,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg563 sg563

lemma sg5287 : RowSquare [4,4,2,2,2,2,1,1] [5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg100 sg1650

lemma sg5288 : RowSquare [4,4,2,2,2,2,1,1] [5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg1651

lemma sg5289 : RowSquare [4,4,2,2,2,2,1,1] [5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg1650

lemma sg5290 : RowSquare [4,4,2,2,2,2,1,1] [5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg99 sg1651

lemma sg5291 : RowSquare [4,4,2,2,2,2,1,1] [6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg102 sg1650

lemma sg5292 : RowSquare [4,4,2,2,2,2,1,1] [7,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg1650

lemma sg5293 : RowSquare [4,4,2,2,2,2,2] [6,6,6] := by
  exact rowSquare_join (by decide) sg83 sg1658

lemma sg5294 : RowSquare [4,4,3,2,1,1,1,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg390 sg833

lemma sg5295 : RowSquare [4,4,3,2,1,1,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg616 sg551

lemma sg5296 : RowSquare [4,4,3,2,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg381 sg849

lemma sg5297 : RowSquare [4,4,3,2,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg849

lemma sg5298 : RowSquare [4,4,3,2,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg2107

lemma sg5299 : RowSquare [4,4,3,2,1,1,1,1,1] [6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg555

lemma sg5300 : RowSquare [4,4,3,2,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg2108

lemma sg5301 : RowSquare [4,4,3,2,2,2,1] [3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg1654

lemma sg5302 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg708

lemma sg5303 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg413 sg998

lemma sg5304 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg710

lemma sg5305 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg413 sg1001

lemma sg5306 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg415 sg998

lemma sg5307 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg414 sg1000

lemma sg5308 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,2] := by
  exact rowSquare_join (by decide) sg414 sg1001

lemma sg5309 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg415 sg999

lemma sg5310 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg415 sg1000

lemma sg5311 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg415 sg1001

lemma sg5312 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg711

lemma sg5313 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg708

lemma sg5314 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg712

lemma sg5315 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg709

lemma sg5316 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg708

lemma sg5317 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg710

lemma sg5318 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg416 sg999

lemma sg5319 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg708

lemma sg5320 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg416 sg1000

lemma sg5321 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,2] := by
  exact rowSquare_join (by decide) sg590 sg708

lemma sg5322 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg713

lemma sg5323 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg417 sg998

lemma sg5324 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg709

lemma sg5325 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg413 sg1006

lemma sg5326 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg710

end UniversalTensorSquare
end
end

end OAI
