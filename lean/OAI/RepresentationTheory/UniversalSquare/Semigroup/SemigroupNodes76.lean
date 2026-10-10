import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 76. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg30940 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9958

lemma sg30941 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10393

lemma sg30942 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9634

lemma sg30943 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14520

lemma sg30944 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3773 sg14542

lemma sg30945 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6953 sg11476

lemma sg30946 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6582 sg11542

lemma sg30947 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9301

lemma sg30948 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9366

lemma sg30949 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9293

lemma sg30950 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9557

lemma sg30951 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6954 sg11476

lemma sg30952 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6583 sg11542

lemma sg30953 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10494

lemma sg30954 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9301

lemma sg30955 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10827

lemma sg30956 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10494

lemma sg30957 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9303

lemma sg30958 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9368

lemma sg30959 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9983

lemma sg30960 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10163

lemma sg30961 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9983

lemma sg30962 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9959

lemma sg30963 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9959

lemma sg30964 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10394

lemma sg30965 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6584 sg11542

lemma sg30966 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10408

lemma sg30967 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10408

lemma sg30968 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9984

lemma sg30969 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10408

lemma sg30970 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9984

lemma sg30971 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9303

lemma sg30972 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9960

lemma sg30973 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9960

lemma sg30974 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10395

lemma sg30975 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9302

lemma sg30976 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9303

lemma sg30977 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9303

lemma sg30978 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10396

lemma sg30979 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9304

lemma sg30980 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9961

lemma sg30981 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9961

lemma sg30982 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10396

lemma sg30983 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9304

lemma sg30984 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9304

lemma sg30985 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,5,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9562

lemma sg30986 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1831 sg17122

lemma sg30987 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2199 sg15571

lemma sg30988 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2240 sg15534

lemma sg30989 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3891 sg14510

lemma sg30990 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2874 sg14857

lemma sg30991 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6996 sg11469

lemma sg30992 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5594 sg12611

lemma sg30993 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9297

lemma sg30994 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8586 sg10101

lemma sg30995 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8666 sg9810

lemma sg30996 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2241 sg15534

lemma sg30997 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3892 sg14510

lemma sg30998 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3771 sg14543

lemma sg30999 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6997 sg11469

lemma sg31000 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5994 sg11834

lemma sg31001 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10390

lemma sg31002 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9297

lemma sg31003 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8660 sg9815

lemma sg31004 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3766 sg14544

lemma sg31005 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6998 sg11469

lemma sg31006 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6593 sg11541

lemma sg31007 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10397

lemma sg31008 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9369

lemma sg31009 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9297

lemma sg31010 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8737 sg9558

lemma sg31011 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6594 sg11541

lemma sg31012 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10495

lemma sg31013 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9266

lemma sg31014 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10828

lemma sg31015 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10495

lemma sg31016 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9267

lemma sg31017 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9985

lemma sg31018 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10164

lemma sg31019 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9985

lemma sg31020 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9962

lemma sg31021 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10397

lemma sg31022 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3893 sg14510

lemma sg31023 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3767 sg14544

lemma sg31024 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6999 sg11469

lemma sg31025 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6595 sg11541

lemma sg31026 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10391

lemma sg31027 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9369

lemma sg31028 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9297

lemma sg31029 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9558

lemma sg31030 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7000 sg11469

lemma sg31031 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6596 sg11541

lemma sg31032 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10496

lemma sg31033 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9370

lemma sg31034 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10829

lemma sg31035 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10496

lemma sg31036 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10409

lemma sg31037 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10409

lemma sg31038 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9986

lemma sg31039 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10409

lemma sg31040 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9986

lemma sg31041 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9963

lemma sg31042 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9963

lemma sg31043 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10398

lemma sg31044 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6597 sg11541

lemma sg31045 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10399

lemma sg31046 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9371

lemma sg31047 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9987

lemma sg31048 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10165

lemma sg31049 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9987

lemma sg31050 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9372

lemma sg31051 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9964

lemma sg31052 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9964

lemma sg31053 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10399

lemma sg31054 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9635

lemma sg31055 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9958

lemma sg31056 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9636

lemma sg31057 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3768 sg14544

lemma sg31058 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7002 sg11468

lemma sg31059 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6598 sg11541

lemma sg31060 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10497

lemma sg31061 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9370

lemma sg31062 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10830

lemma sg31063 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10497

lemma sg31064 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6599 sg11541

lemma sg31065 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10410

lemma sg31066 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10410

lemma sg31067 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9988

lemma sg31068 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10410

lemma sg31069 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9988

lemma sg31070 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9372

lemma sg31071 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9965

lemma sg31072 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9965

lemma sg31073 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9637

lemma sg31074 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10401

lemma sg31075 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9374

lemma sg31076 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9966

lemma sg31077 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9966

lemma sg31078 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9960

lemma sg31079 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9638

lemma sg31080 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9636

lemma sg31081 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9375

lemma sg31082 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9961

lemma sg31083 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9639

lemma sg31084 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8808 sg9304

lemma sg31085 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7003 sg11468

lemma sg31086 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6001 sg11833

lemma sg31087 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9310

lemma sg31088 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9373

lemma sg31089 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9989

lemma sg31090 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10166

lemma sg31091 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9989

lemma sg31092 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10402

lemma sg31093 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9310

lemma sg31094 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9967

lemma sg31095 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9967

lemma sg31096 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9310

lemma sg31097 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9310

lemma sg31098 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9311

lemma sg31099 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9311

lemma sg31100 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9311

lemma sg31101 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9638

lemma sg31102 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9961

lemma sg31103 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9639

lemma sg31104 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9639

lemma sg31105 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,7,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9990

lemma sg31106 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,7,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10722

lemma sg31107 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,7,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9991

lemma sg31108 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,7,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9992

lemma sg31109 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,8,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9993

lemma sg31110 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,8,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9994

lemma sg31111 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,9,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8193 sg10863

lemma sg31112 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg990 sg21108

lemma sg31113 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1317 sg20976

lemma sg31114 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg985 sg21111

lemma sg31115 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg562 sg21250

lemma sg31116 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg21139

lemma sg31117 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg21289

lemma sg31118 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg21290

lemma sg31119 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg21291

lemma sg31120 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg21292

lemma sg31121 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg407 sg21293

lemma sg31122 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1322 sg20965

lemma sg31123 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1725 sg18245

lemma sg31124 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg20938

lemma sg31125 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1827 sg17124

lemma sg31126 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2237 sg15536

lemma sg31127 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2680 sg15022

lemma sg31128 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg871 sg21144

lemma sg31129 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14694

lemma sg31130 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg871 sg21145

lemma sg31131 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg871 sg21146

lemma sg31132 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg871 sg21147

lemma sg31133 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg986 sg21111

lemma sg31134 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1837 sg17110

lemma sg31135 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1849 sg16208

lemma sg31136 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2223 sg15550

lemma sg31137 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2867 sg14864

lemma sg31138 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5599 sg12609

lemma sg31139 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg972 sg21125

lemma sg31140 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8583 sg10105

lemma sg31141 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6891 sg11505

lemma sg31142 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg20939

lemma sg31143 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2246 sg15516

lemma sg31144 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1297 sg20997

lemma sg31145 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5583 sg12620

lemma sg31146 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1297 sg20998

lemma sg31147 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7255 sg11440

lemma sg31148 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1297 sg20999

lemma sg31149 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8657 sg9844

lemma sg31150 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg16207

lemma sg31151 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5844 sg11840

lemma sg31152 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6585 sg11542

lemma sg31153 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8584 sg10105

lemma sg31154 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9198

lemma sg31155 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8736 sg9580

lemma sg31156 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6586 sg11542

lemma sg31157 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8585 sg10105

lemma sg31158 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9199

lemma sg31159 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9975

lemma sg31160 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8777 sg9450

lemma sg31161 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7240 sg11453

lemma sg31162 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8659 sg9844

lemma sg31163 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8650 sg9975

lemma sg31164 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8859 sg9162

lemma sg31165 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg7232 sg11466

lemma sg31166 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1726 sg18245

lemma sg31167 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1837 sg17111

lemma sg31168 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2206 sg15564

lemma sg31169 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2238 sg15536

lemma sg31170 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2681 sg15022

lemma sg31171 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2868 sg14864

lemma sg31172 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5566 sg12630

lemma sg31173 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2667 sg15035

lemma sg31174 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8453 sg10308

lemma sg31175 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8386 sg10641

lemma sg31176 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1829 sg17124

lemma sg31177 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2239 sg15536

lemma sg31178 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2682 sg15022

lemma sg31179 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14864

lemma sg31180 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5567 sg12630

lemma sg31181 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1298 sg20998

lemma sg31182 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7249 sg11449

lemma sg31183 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1298 sg20999

lemma sg31184 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8660 sg9844

lemma sg31185 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2683 sg15022

lemma sg31186 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2361 sg15483

lemma sg31187 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5845 sg11840

lemma sg31188 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6587 sg11542

lemma sg31189 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10403

lemma sg31190 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9380

lemma sg31191 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8657 sg9845

lemma sg31192 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5846 sg11840

lemma sg31193 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6588 sg11542

lemma sg31194 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8588 sg10105

lemma sg31195 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9201

lemma sg31196 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9975

lemma sg31197 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8736 sg9581

lemma sg31198 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10498

lemma sg31199 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9202

lemma sg31200 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10831

lemma sg31201 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10498

lemma sg31202 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8674 sg9730

lemma sg31203 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9976

lemma sg31204 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8678 sg9662

lemma sg31205 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1868 sg16190

lemma sg31206 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3169 sg14805

lemma sg31207 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3777 sg14542

lemma sg31208 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5847 sg11840

lemma sg31209 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6589 sg11542

lemma sg31210 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8590 sg10105

lemma sg31211 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9380

lemma sg31212 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8739 sg9580

lemma sg31213 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3778 sg14542

lemma sg31214 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5584 sg12620

lemma sg31215 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6590 sg11542

lemma sg31216 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8591 sg10105

lemma sg31217 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9294

lemma sg31218 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9975

lemma sg31219 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8763 sg9495

lemma sg31220 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6591 sg11542

lemma sg31221 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8592 sg10105

lemma sg31222 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9295

lemma sg31223 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8740 sg9580

lemma sg31224 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9640

lemma sg31225 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9296

lemma sg31226 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9977

lemma sg31227 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8843 sg9199

lemma sg31228 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8658 sg9846

lemma sg31229 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9977

lemma sg31230 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5585 sg12620

lemma sg31231 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6592 sg11542

lemma sg31232 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10499

lemma sg31233 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8400 sg10602

lemma sg31234 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10832

lemma sg31235 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10499

lemma sg31236 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8594 sg10105

lemma sg31237 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8401 sg10602

lemma sg31238 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9847

lemma sg31239 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9583

lemma sg31240 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8675 sg9729

lemma sg31241 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9978

lemma sg31242 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9978

lemma sg31243 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6893 sg11505

lemma sg31244 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9979

lemma sg31245 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9979

lemma sg31246 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,4,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9584

lemma sg31247 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1838 sg17111

lemma sg31248 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2207 sg15564

lemma sg31249 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2240 sg15536

lemma sg31250 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2684 sg15022

lemma sg31251 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2876 sg14857

lemma sg31252 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5570 sg12630

lemma sg31253 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1299 sg20998

lemma sg31254 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7251 sg11449

lemma sg31255 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1299 sg20999

lemma sg31256 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8666 sg9844

lemma sg31257 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2241 sg15536

lemma sg31258 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3169 sg14806

lemma sg31259 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3777 sg14543

lemma sg31260 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5571 sg12630

lemma sg31261 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5250 sg12695

lemma sg31262 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10403

lemma sg31263 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9297

lemma sg31264 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8660 sg9845

lemma sg31265 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3766 sg14545

lemma sg31266 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5848 sg11840

lemma sg31267 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6593 sg11542

lemma sg31268 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10405

lemma sg31269 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9381

lemma sg31270 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9848

lemma sg31271 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8737 sg9581

lemma sg31272 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6594 sg11542

lemma sg31273 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10500

lemma sg31274 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9295

lemma sg31275 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10833

lemma sg31276 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10500

lemma sg31277 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9296

lemma sg31278 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9980

lemma sg31279 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9641

lemma sg31280 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8658 sg9848

lemma sg31281 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9980

lemma sg31282 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3171 sg14805

lemma sg31283 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3767 sg14545

lemma sg31284 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5849 sg11840

lemma sg31285 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6595 sg11542

lemma sg31286 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8595 sg10105

lemma sg31287 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9381

lemma sg31288 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8660 sg9846

lemma sg31289 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9581

lemma sg31290 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5573 sg12630

lemma sg31291 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6596 sg11542

lemma sg31292 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10501

lemma sg31293 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9382

lemma sg31294 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10834

lemma sg31295 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10501

lemma sg31296 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8596 sg10105

lemma sg31297 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9300

lemma sg31298 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9977

lemma sg31299 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9641

lemma sg31300 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8818 sg9293

lemma sg31301 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9981

lemma sg31302 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9981

lemma sg31303 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6597 sg11542

lemma sg31304 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10407

lemma sg31305 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9383

lemma sg31306 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9850

lemma sg31307 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9641

lemma sg31308 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8675 sg9733

lemma sg31309 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9384

lemma sg31310 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9982

lemma sg31311 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9982

lemma sg31312 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9642

lemma sg31313 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9979

lemma sg31314 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9643

lemma sg31315 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3768 sg14545

lemma sg31316 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5586 sg12620

lemma sg31317 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6598 sg11542

lemma sg31318 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8597 sg10105

lemma sg31319 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9382

lemma sg31320 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8765 sg9494

lemma sg31321 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8819 sg9293

lemma sg31322 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6599 sg11542

lemma sg31323 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8598 sg10105

lemma sg31324 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9383

lemma sg31325 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9977

lemma sg31326 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9294

lemma sg31327 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9384

lemma sg31328 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9983

lemma sg31329 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9983

lemma sg31330 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9296

lemma sg31331 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10408

lemma sg31332 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9304

lemma sg31333 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9984

lemma sg31334 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9984

lemma sg31335 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9979

lemma sg31336 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9642

lemma sg31337 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9643

lemma sg31338 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8402 sg10602

lemma sg31339 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9855

end UniversalTensorSquare
end
end

end OAI
