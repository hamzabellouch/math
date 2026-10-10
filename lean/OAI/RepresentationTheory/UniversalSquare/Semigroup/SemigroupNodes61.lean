import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 61. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24940 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2686 sg15011

lemma sg24941 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2695 sg15004

lemma sg24942 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5551 sg12621

lemma sg24943 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5253 sg12687

lemma sg24944 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8595 sg10081

lemma sg24945 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9211

lemma sg24946 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9667

lemma sg24947 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9459

lemma sg24948 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5552 sg12621

lemma sg24949 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5254 sg12687

lemma sg24950 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10243

lemma sg24951 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9215

lemma sg24952 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9744

lemma sg24953 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8544 sg10095

lemma sg24954 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8596 sg10081

lemma sg24955 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9213

lemma sg24956 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9749

lemma sg24957 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9512

lemma sg24958 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8180 sg10857

lemma sg24959 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9759

lemma sg24960 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9759

lemma sg24961 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8823 sg9165

lemma sg24962 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9669

lemma sg24963 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9060

lemma sg24964 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5255 sg12687

lemma sg24965 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10244

lemma sg24966 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9216

lemma sg24967 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9745

lemma sg24968 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9512

lemma sg24969 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8370 sg10607

lemma sg24970 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9217

lemma sg24971 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9760

lemma sg24972 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9760

lemma sg24973 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8818 sg9171

lemma sg24974 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9516

lemma sg24975 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10243

lemma sg24976 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9061

lemma sg24977 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10651

lemma sg24978 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9751

lemma sg24979 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9517

lemma sg24980 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8661 sg9679

lemma sg24981 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9062

lemma sg24982 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10241

lemma sg24983 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10652

lemma sg24984 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8662 sg9679

lemma sg24985 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8738 sg9465

lemma sg24986 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8459 sg10193

lemma sg24987 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8599 sg10080

lemma sg24988 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9218

lemma sg24989 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9761

lemma sg24990 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9761

lemma sg24991 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8663 sg9677

lemma sg24992 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9752

lemma sg24993 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9518

lemma sg24994 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10244

lemma sg24995 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9063

lemma sg24996 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9678

lemma sg24997 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8430 sg10240

lemma sg24998 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,3,3,3] := by
  exact rowSquare_join (by decide) sg8662 sg9680

lemma sg24999 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9515

lemma sg25000 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10242

lemma sg25001 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8352 sg10651

lemma sg25002 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10241

lemma sg25003 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg8662 sg9681

lemma sg25004 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6893 sg11498

lemma sg25005 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg8545 sg10098

lemma sg25006 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7247 sg11443

lemma sg25007 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8748 sg9451

lemma sg25008 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8526 sg10115

lemma sg25009 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8745 sg9456

lemma sg25010 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9064

lemma sg25011 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9515

lemma sg25012 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8661 sg9682

lemma sg25013 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8741 sg9462

lemma sg25014 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8864 sg9002

lemma sg25015 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10242

lemma sg25016 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10242

lemma sg25017 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,6,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1462 sg20934

lemma sg25018 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2696 sg15004

lemma sg25019 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5577 sg12614

lemma sg25020 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5256 sg12687

lemma sg25021 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8597 sg10081

lemma sg25022 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9215

lemma sg25023 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7786 sg11248

lemma sg25024 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8547 sg10095

lemma sg25025 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5257 sg12687

lemma sg25026 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8598 sg10081

lemma sg25027 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9216

lemma sg25028 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9749

lemma sg25029 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9171

lemma sg25030 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7242 sg11447

lemma sg25031 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9217

lemma sg25032 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8746 sg9453

lemma sg25033 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10127

lemma sg25034 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8548 sg10095

lemma sg25035 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8739 sg9465

lemma sg25036 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8549 sg10095

lemma sg25037 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8870 sg8990

lemma sg25038 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8189 sg10853

lemma sg25039 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8599 sg10081

lemma sg25040 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9218

lemma sg25041 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9750

lemma sg25042 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10128

lemma sg25043 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8370 sg10610

lemma sg25044 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9751

lemma sg25045 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9516

lemma sg25046 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9679

lemma sg25047 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8865 sg8999

lemma sg25048 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10243

lemma sg25049 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10653

lemma sg25050 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8672 sg9669

lemma sg25051 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9517

lemma sg25052 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8746 sg9455

lemma sg25053 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8740 sg9464

lemma sg25054 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8740 sg9465

lemma sg25055 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8396 sg10599

lemma sg25056 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9752

lemma sg25057 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9516

lemma sg25058 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9680

lemma sg25059 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8371 sg10610

lemma sg25060 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9518

lemma sg25061 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10244

lemma sg25062 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8865 sg9000

lemma sg25063 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10243

lemma sg25064 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8747 sg9455

lemma sg25065 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8352 sg10653

lemma sg25066 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg8548 sg10098

lemma sg25067 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8767 sg9444

lemma sg25068 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8527 sg10115

lemma sg25069 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9682

lemma sg25070 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8741 sg9466

lemma sg25071 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10244

lemma sg25072 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10244

lemma sg25073 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8460 sg10195

lemma sg25074 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8528 sg10115

lemma sg25075 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,7,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8748 sg9456

lemma sg25076 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,7,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8741 sg9468

lemma sg25077 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,7,7,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8461 sg10195

lemma sg25078 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1723 sg18243

lemma sg25079 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1831 sg17105

lemma sg25080 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1831 sg17106

lemma sg25081 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1850 sg16201

lemma sg25082 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15521

lemma sg25083 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2868 sg14852

lemma sg25084 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg21210

lemma sg25085 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg21211

lemma sg25086 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg21212

lemma sg25087 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg658 sg21213

lemma sg25088 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2199 sg15561

lemma sg25089 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1851 sg16201

lemma sg25090 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2225 sg15521

lemma sg25091 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14852

lemma sg25092 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3515 sg14680

lemma sg25093 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg966 sg21121

lemma sg25094 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6294 sg11742

lemma sg25095 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg966 sg21122

lemma sg25096 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6361 sg11739

lemma sg25097 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2226 sg15521

lemma sg25098 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1817 sg17113

lemma sg25099 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4692 sg12937

lemma sg25100 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4622 sg12945

lemma sg25101 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6734 sg11508

lemma sg25102 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8183 sg10854

lemma sg25103 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8666 sg9672

lemma sg25104 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3516 sg14680

lemma sg25105 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5268 sg12680

lemma sg25106 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1706 sg18246

lemma sg25107 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8228 sg10848

lemma sg25108 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1706 sg18247

lemma sg25109 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8507 sg10167

lemma sg25110 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6914 sg11470

lemma sg25111 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8184 sg10854

lemma sg25112 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9673

lemma sg25113 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8526 sg10116

lemma sg25114 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8463 sg10190

lemma sg25115 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8488 sg10170

lemma sg25116 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg554 sg21252

lemma sg25117 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8860 sg9065

lemma sg25118 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2242 sg15512

lemma sg25119 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2687 sg15011

lemma sg25120 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2870 sg14852

lemma sg25121 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4680 sg12939

lemma sg25122 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5250 sg12688

lemma sg25123 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6735 sg11508

lemma sg25124 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8185 sg10854

lemma sg25125 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8666 sg9674

lemma sg25126 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2871 sg14852

lemma sg25127 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4681 sg12939

lemma sg25128 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5251 sg12688

lemma sg25129 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2877 sg14819

lemma sg25130 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9219

lemma sg25131 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2173 sg15575

lemma sg25132 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8742 sg9457

lemma sg25133 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5252 sg12688

lemma sg25134 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6915 sg11470

lemma sg25135 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8186 sg10854

lemma sg25136 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9675

lemma sg25137 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8527 sg10116

lemma sg25138 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8187 sg10854

lemma sg25139 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9676

lemma sg25140 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9519

lemma sg25141 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg11462

lemma sg25142 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8742 sg9458

lemma sg25143 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg7245 sg11445

lemma sg25144 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9066

lemma sg25145 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4692 sg12938

lemma sg25146 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5268 sg12681

lemma sg25147 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8254 sg10844

lemma sg25148 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8188 sg10854

lemma sg25149 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9677

lemma sg25150 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8528 sg10116

lemma sg25151 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8255 sg10844

lemma sg25152 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9220

lemma sg25153 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9753

lemma sg25154 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8669 sg9672

lemma sg25155 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8820 sg9166

lemma sg25156 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9678

lemma sg25157 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9520

lemma sg25158 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9167

lemma sg25159 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg571 sg21222

lemma sg25160 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9067

lemma sg25161 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8398 sg10598

lemma sg25162 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9754

lemma sg25163 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8489 sg10170

lemma sg25164 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8821 sg9166

lemma sg25165 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9521

lemma sg25166 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8822 sg9166

lemma sg25167 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9068

lemma sg25168 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8465 sg10190

lemma sg25169 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg7785 sg11249

lemma sg25170 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8822 sg9167

lemma sg25171 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg8743 sg9458

lemma sg25172 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2688 sg15011

lemma sg25173 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2697 sg15004

lemma sg25174 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4682 sg12939

lemma sg25175 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5253 sg12688

lemma sg25176 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2878 sg14819

lemma sg25177 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9219

lemma sg25178 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4929 sg12816

lemma sg25179 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8742 sg9459

lemma sg25180 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4683 sg12939

lemma sg25181 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5254 sg12688

lemma sg25182 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8254 sg10845

lemma sg25183 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6120 sg11767

lemma sg25184 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7783 sg11250

lemma sg25185 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8668 sg9674

lemma sg25186 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8255 sg10845

lemma sg25187 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9220

lemma sg25188 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9755

lemma sg25189 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9519

lemma sg25190 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8823 sg9166

lemma sg25191 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8463 sg10193

lemma sg25192 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9522

lemma sg25193 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8823 sg9167

lemma sg25194 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8466 sg10190

lemma sg25195 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9069

lemma sg25196 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5255 sg12688

lemma sg25197 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8257 sg10844

lemma sg25198 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9221

lemma sg25199 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9753

lemma sg25200 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9519

lemma sg25201 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8820 sg9168

lemma sg25202 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9222

lemma sg25203 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9756

lemma sg25204 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9520

lemma sg25205 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9169

lemma sg25206 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9523

lemma sg25207 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9676

lemma sg25208 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9070

lemma sg25209 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8467 sg10190

lemma sg25210 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9757

lemma sg25211 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9524

lemma sg25212 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8824 sg9166

lemma sg25213 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9071

lemma sg25214 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8553 sg10092

lemma sg25215 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8669 sg9676

lemma sg25216 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8744 sg9458

lemma sg25217 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8869 sg8995

lemma sg25218 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8258 sg10844

lemma sg25219 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9223

lemma sg25220 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9682

lemma sg25221 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9520

lemma sg25222 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9170

lemma sg25223 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9758

lemma sg25224 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9525

lemma sg25225 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8373 sg10609

lemma sg25226 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9072

lemma sg25227 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9678

lemma sg25228 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8822 sg9170

lemma sg25229 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg8745 sg9458

lemma sg25230 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8489 sg10172

lemma sg25231 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8375 sg10606

lemma sg25232 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8867 sg8996

lemma sg25233 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8867 sg8997

lemma sg25234 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10606

lemma sg25235 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg8867 sg8998

lemma sg25236 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2698 sg15004

lemma sg25237 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4684 sg12939

lemma sg25238 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5256 sg12688

lemma sg25239 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8256 sg10845

lemma sg25240 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6121 sg11767

lemma sg25241 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7786 sg11250

lemma sg25242 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8670 sg9674

lemma sg25243 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5257 sg12688

lemma sg25244 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8257 sg10845

lemma sg25245 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9224

lemma sg25246 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9755

lemma sg25247 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8671 sg9674

lemma sg25248 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8183 sg10857

lemma sg25249 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9222

lemma sg25250 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9759

lemma sg25251 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9522

lemma sg25252 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8823 sg9169

lemma sg25253 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9526

lemma sg25254 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9676

lemma sg25255 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9073

lemma sg25256 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg7453 sg11281

lemma sg25257 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8258 sg10845

lemma sg25258 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9225

lemma sg25259 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9756

lemma sg25260 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9522

lemma sg25261 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9171

lemma sg25262 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9760

lemma sg25263 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9527

lemma sg25264 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9679

lemma sg25265 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9074

lemma sg25266 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9678

lemma sg25267 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8671 sg9676

lemma sg25268 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9524

lemma sg25269 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8556 sg10092

lemma sg25270 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8669 sg9679

lemma sg25271 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8465 sg10193

lemma sg25272 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9226

lemma sg25273 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9761

lemma sg25274 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9528

lemma sg25275 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9680

lemma sg25276 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9075

lemma sg25277 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9525

lemma sg25278 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9681

lemma sg25279 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8867 sg9000

lemma sg25280 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8868 sg8997

lemma sg25281 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10607

lemma sg25282 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8867 sg9001

lemma sg25283 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10608

lemma sg25284 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8768 sg9444

lemma sg25285 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9525

lemma sg25286 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9682

lemma sg25287 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8825 sg9170

lemma sg25288 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10092

lemma sg25289 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8867 sg9002

lemma sg25290 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8465 sg10195

lemma sg25291 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14502

lemma sg25292 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4623 sg12946

lemma sg25293 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8259 sg10845

lemma sg25294 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9224

lemma sg25295 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7450 sg11351

lemma sg25296 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8189 sg10855

lemma sg25297 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8185 sg10857

lemma sg25298 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8260 sg10845

lemma sg25299 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9227

lemma sg25300 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9759

lemma sg25301 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8672 sg9674

lemma sg25302 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8823 sg9171

lemma sg25303 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8769 sg9442

lemma sg25304 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9529

lemma sg25305 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9679

lemma sg25306 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9076

lemma sg25307 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8466 sg10193

lemma sg25308 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8189 sg10856

lemma sg25309 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9228

lemma sg25310 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9760

lemma sg25311 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9530

lemma sg25312 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9680

lemma sg25313 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9077

lemma sg25314 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9527

lemma sg25315 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9681

lemma sg25316 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8671 sg9679

lemma sg25317 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8467 sg10193

lemma sg25318 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7788 sg11251

lemma sg25319 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8870 sg8998

lemma sg25320 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9761

lemma sg25321 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9528

lemma sg25322 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9682

lemma sg25323 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8868 sg9000

lemma sg25324 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8466 sg10195

lemma sg25325 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8868 sg9001

lemma sg25326 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10610

lemma sg25327 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9528

lemma sg25328 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10093

lemma sg25329 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8868 sg9002

lemma sg25330 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8467 sg10195

lemma sg25331 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,7,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7789 sg11252

lemma sg25332 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,7,7,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8748 sg9461

lemma sg25333 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1868 sg16188

lemma sg25334 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7254 sg11434

lemma sg25335 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9227

lemma sg25336 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7786 sg11253

lemma sg25337 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7794 sg11244

lemma sg25338 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8189 sg10857

lemma sg25339 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9228

end UniversalTensorSquare
end
end

end OAI
