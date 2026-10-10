import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData62
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupMissingLeaves
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes100
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes101
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes102
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes103
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes104
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes105
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes106
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes79
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes80
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes81
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes82
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes83
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes84
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes85
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes86
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes87
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes88
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes89
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes90
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes91
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes92
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes93
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes94
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes95
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes96
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes97
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes98
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes99

namespace OAI

/-! Degree Tree Proof 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree62_0All : degreeTree62_0.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32016,⟨sg32011,⟨sg32008,⟨sg32007,⟨sg32006,True.intro,True.intro⟩,True.intro⟩,⟨sg32010,⟨sg32009,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32014,⟨sg32013,⟨sg32012,True.intro,True.intro⟩,True.intro⟩,⟨sg32015,True.intro,True.intro⟩⟩⟩,⟨sg32022,⟨sg32019,⟨sg32018,⟨sg32017,True.intro,True.intro⟩,True.intro⟩,⟨sg32021,⟨sg32020,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32025,⟨sg32024,⟨sg32023,True.intro,True.intro⟩,True.intro⟩,⟨sg32026,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1All : degreeTree62_1.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32038,⟨sg32033,⟨sg32030,⟨sg32029,⟨sg32028,True.intro,True.intro⟩,True.intro⟩,⟨sg32032,⟨sg32031,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32036,⟨sg32035,⟨sg32034,True.intro,True.intro⟩,True.intro⟩,⟨sg32037,True.intro,True.intro⟩⟩⟩,⟨sg32044,⟨sg32041,⟨sg32040,⟨sg32039,True.intro,True.intro⟩,True.intro⟩,⟨sg32043,⟨sg32042,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32047,⟨sg32046,⟨sg32045,True.intro,True.intro⟩,True.intro⟩,⟨sg32048,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_2All : degreeTree62_2.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32027,degreeTree62_0All,degreeTree62_1All⟩

lemma degreeTree62_3All : degreeTree62_3.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32060,⟨sg32055,⟨sg32052,⟨sg32051,⟨sg32050,True.intro,True.intro⟩,True.intro⟩,⟨sg32054,⟨sg32053,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32058,⟨sg32057,⟨sg32056,True.intro,True.intro⟩,True.intro⟩,⟨sg32059,True.intro,True.intro⟩⟩⟩,⟨sg32066,⟨sg32063,⟨sg32062,⟨sg32061,True.intro,True.intro⟩,True.intro⟩,⟨sg32065,⟨sg32064,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32069,⟨sg32068,⟨sg32067,True.intro,True.intro⟩,True.intro⟩,⟨sg32070,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_4All : degreeTree62_4.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32082,⟨sg32077,⟨sg32074,⟨sg32073,⟨sg32072,True.intro,True.intro⟩,True.intro⟩,⟨sg32076,⟨sg32075,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32080,⟨sg32079,⟨sg32078,True.intro,True.intro⟩,True.intro⟩,⟨sg32081,True.intro,True.intro⟩⟩⟩,⟨sg32088,⟨sg32085,⟨sg32084,⟨sg32083,True.intro,True.intro⟩,True.intro⟩,⟨sg32087,⟨sg32086,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32091,⟨sg32090,⟨sg32089,True.intro,True.intro⟩,True.intro⟩,⟨sg32092,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_5All : degreeTree62_5.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32071,degreeTree62_3All,degreeTree62_4All⟩

lemma degreeTree62_6All : degreeTree62_6.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32049,degreeTree62_2All,degreeTree62_5All⟩

lemma degreeTree62_7All : degreeTree62_7.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32104,⟨sg32099,⟨sg32096,⟨sg32095,⟨sg32094,True.intro,True.intro⟩,True.intro⟩,⟨sg32098,⟨sg32097,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32102,⟨sg32101,⟨sg32100,True.intro,True.intro⟩,True.intro⟩,⟨sg32103,True.intro,True.intro⟩⟩⟩,⟨sg32110,⟨sg32107,⟨sg32106,⟨sg32105,True.intro,True.intro⟩,True.intro⟩,⟨sg32109,⟨sg32108,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32113,⟨sg32112,⟨sg32111,True.intro,True.intro⟩,True.intro⟩,⟨sg32114,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_8All : degreeTree62_8.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32126,⟨sg32121,⟨sg32118,⟨sg32117,⟨sg32116,True.intro,True.intro⟩,True.intro⟩,⟨sg32120,⟨sg32119,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32124,⟨sg32123,⟨sg32122,True.intro,True.intro⟩,True.intro⟩,⟨sg32125,True.intro,True.intro⟩⟩⟩,⟨sg32132,⟨sg32129,⟨sg32128,⟨sg32127,True.intro,True.intro⟩,True.intro⟩,⟨sg32131,⟨sg32130,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32135,⟨sg32134,⟨sg32133,True.intro,True.intro⟩,True.intro⟩,⟨sg32136,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_9All : degreeTree62_9.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32115,degreeTree62_7All,degreeTree62_8All⟩

lemma degreeTree62_10All : degreeTree62_10.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32148,⟨sg32143,⟨sg32140,⟨sg32139,⟨sg32138,True.intro,True.intro⟩,True.intro⟩,⟨sg32142,⟨sg32141,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32146,⟨sg32145,⟨sg32144,True.intro,True.intro⟩,True.intro⟩,⟨sg32147,True.intro,True.intro⟩⟩⟩,⟨sg32154,⟨sg32151,⟨sg32150,⟨sg32149,True.intro,True.intro⟩,True.intro⟩,⟨sg32153,⟨sg32152,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32157,⟨sg32156,⟨sg32155,True.intro,True.intro⟩,True.intro⟩,⟨sg32158,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_11All : degreeTree62_11.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32170,⟨sg32165,⟨sg32162,⟨sg32161,⟨sg32160,True.intro,True.intro⟩,True.intro⟩,⟨sg32164,⟨sg32163,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32168,⟨sg32167,⟨sg32166,True.intro,True.intro⟩,True.intro⟩,⟨sg32169,True.intro,True.intro⟩⟩⟩,⟨sg32176,⟨sg32173,⟨sg32172,⟨sg32171,True.intro,True.intro⟩,True.intro⟩,⟨sg32175,⟨sg32174,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32179,⟨sg32178,⟨sg32177,True.intro,True.intro⟩,True.intro⟩,⟨sg32180,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_12All : degreeTree62_12.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32159,degreeTree62_10All,degreeTree62_11All⟩

lemma degreeTree62_13All : degreeTree62_13.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32137,degreeTree62_9All,degreeTree62_12All⟩

lemma degreeTree62_14All : degreeTree62_14.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32093,degreeTree62_6All,degreeTree62_13All⟩

lemma degreeTree62_15All : degreeTree62_15.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32192,⟨sg32187,⟨sg32184,⟨sg32183,⟨sg32182,True.intro,True.intro⟩,True.intro⟩,⟨sg32186,⟨sg32185,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32190,⟨sg32189,⟨sg32188,True.intro,True.intro⟩,True.intro⟩,⟨sg32191,True.intro,True.intro⟩⟩⟩,⟨sg32198,⟨sg32195,⟨sg32194,⟨sg32193,True.intro,True.intro⟩,True.intro⟩,⟨sg32197,⟨sg32196,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32201,⟨sg32200,⟨sg32199,True.intro,True.intro⟩,True.intro⟩,⟨sg32202,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_16All : degreeTree62_16.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32214,⟨sg32209,⟨sg32206,⟨sg32205,⟨sg32204,True.intro,True.intro⟩,True.intro⟩,⟨sg32208,⟨sg32207,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32212,⟨sg32211,⟨sg32210,True.intro,True.intro⟩,True.intro⟩,⟨sg32213,True.intro,True.intro⟩⟩⟩,⟨sg32220,⟨sg32217,⟨sg32216,⟨sg32215,True.intro,True.intro⟩,True.intro⟩,⟨sg32219,⟨sg32218,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32223,⟨sg32222,⟨sg32221,True.intro,True.intro⟩,True.intro⟩,⟨sg32224,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_17All : degreeTree62_17.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32203,degreeTree62_15All,degreeTree62_16All⟩

lemma degreeTree62_18All : degreeTree62_18.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32236,⟨sg32231,⟨sg32228,⟨sg32227,⟨sg32226,True.intro,True.intro⟩,True.intro⟩,⟨sg32230,⟨sg32229,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32234,⟨sg32233,⟨sg32232,True.intro,True.intro⟩,True.intro⟩,⟨sg32235,True.intro,True.intro⟩⟩⟩,⟨sg32242,⟨sg32239,⟨sg32238,⟨sg32237,True.intro,True.intro⟩,True.intro⟩,⟨sg32241,⟨sg32240,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32245,⟨sg32244,⟨sg32243,True.intro,True.intro⟩,True.intro⟩,⟨sg32246,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_19All : degreeTree62_19.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32258,⟨sg32253,⟨sg32250,⟨sg32249,⟨sg32248,True.intro,True.intro⟩,True.intro⟩,⟨sg32252,⟨sg32251,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32256,⟨sg32255,⟨sg32254,True.intro,True.intro⟩,True.intro⟩,⟨sg32257,True.intro,True.intro⟩⟩⟩,⟨sg32264,⟨sg32261,⟨sg32260,⟨sg32259,True.intro,True.intro⟩,True.intro⟩,⟨sg32263,⟨sg32262,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32267,⟨sg32266,⟨sg32265,True.intro,True.intro⟩,True.intro⟩,⟨sg32268,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_20All : degreeTree62_20.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32247,degreeTree62_18All,degreeTree62_19All⟩

lemma degreeTree62_21All : degreeTree62_21.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32225,degreeTree62_17All,degreeTree62_20All⟩

lemma degreeTree62_22All : degreeTree62_22.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32280,⟨sg32275,⟨sg32272,⟨sg32271,⟨sg32270,True.intro,True.intro⟩,True.intro⟩,⟨sg32274,⟨sg32273,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32278,⟨sg32277,⟨sg32276,True.intro,True.intro⟩,True.intro⟩,⟨sg32279,True.intro,True.intro⟩⟩⟩,⟨sg32286,⟨sg32283,⟨sg32282,⟨sg32281,True.intro,True.intro⟩,True.intro⟩,⟨sg32285,⟨sg32284,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32289,⟨sg32288,⟨sg32287,True.intro,True.intro⟩,True.intro⟩,⟨sg32290,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_23All : degreeTree62_23.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32302,⟨sg32297,⟨sg32294,⟨sg32293,⟨sg32292,True.intro,True.intro⟩,True.intro⟩,⟨sg32296,⟨sg32295,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32300,⟨sg32299,⟨sg32298,True.intro,True.intro⟩,True.intro⟩,⟨sg32301,True.intro,True.intro⟩⟩⟩,⟨sg32308,⟨sg32305,⟨sg32304,⟨sg32303,True.intro,True.intro⟩,True.intro⟩,⟨sg32307,⟨sg32306,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32311,⟨sg32310,⟨sg32309,True.intro,True.intro⟩,True.intro⟩,⟨sg32312,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_24All : degreeTree62_24.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32291,degreeTree62_22All,degreeTree62_23All⟩

lemma degreeTree62_25All : degreeTree62_25.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32324,⟨sg32319,⟨sg32316,⟨sg32315,⟨sg32314,True.intro,True.intro⟩,True.intro⟩,⟨sg32318,⟨sg32317,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32322,⟨sg32321,⟨sg32320,True.intro,True.intro⟩,True.intro⟩,⟨sg32323,True.intro,True.intro⟩⟩⟩,⟨sg32330,⟨sg32327,⟨sg32326,⟨sg32325,True.intro,True.intro⟩,True.intro⟩,⟨sg32329,⟨sg32328,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32333,⟨sg32332,⟨sg32331,True.intro,True.intro⟩,True.intro⟩,⟨sg32334,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_26All : degreeTree62_26.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32346,⟨sg32341,⟨sg32338,⟨sg32337,⟨sg32336,True.intro,True.intro⟩,True.intro⟩,⟨sg32340,⟨sg32339,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32344,⟨sg32343,⟨sg32342,True.intro,True.intro⟩,True.intro⟩,⟨sg32345,True.intro,True.intro⟩⟩⟩,⟨sg32351,⟨sg32349,⟨sg32348,⟨sg32347,True.intro,True.intro⟩,True.intro⟩,⟨sg32350,True.intro,True.intro⟩⟩,⟨sg32354,⟨sg32353,⟨sg32352,True.intro,True.intro⟩,True.intro⟩,⟨sg32355,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_27All : degreeTree62_27.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32335,degreeTree62_25All,degreeTree62_26All⟩

lemma degreeTree62_28All : degreeTree62_28.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32313,degreeTree62_24All,degreeTree62_27All⟩

lemma degreeTree62_29All : degreeTree62_29.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32269,degreeTree62_21All,degreeTree62_28All⟩

lemma degreeTree62_30All : degreeTree62_30.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32181,degreeTree62_14All,degreeTree62_29All⟩

lemma degreeTree62_31All : degreeTree62_31.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32367,⟨sg32362,⟨sg32359,⟨sg32358,⟨sg32357,True.intro,True.intro⟩,True.intro⟩,⟨sg32361,⟨sg32360,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32365,⟨sg32364,⟨sg32363,True.intro,True.intro⟩,True.intro⟩,⟨sg32366,True.intro,True.intro⟩⟩⟩,⟨sg32373,⟨sg32370,⟨sg32369,⟨sg32368,True.intro,True.intro⟩,True.intro⟩,⟨sg32372,⟨sg32371,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32376,⟨sg32375,⟨sg32374,True.intro,True.intro⟩,True.intro⟩,⟨sg32377,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_32All : degreeTree62_32.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32389,⟨sg32384,⟨sg32381,⟨sg32380,⟨sg32379,True.intro,True.intro⟩,True.intro⟩,⟨sg32383,⟨sg32382,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32387,⟨sg32386,⟨sg32385,True.intro,True.intro⟩,True.intro⟩,⟨sg32388,True.intro,True.intro⟩⟩⟩,⟨sg32395,⟨sg32392,⟨sg32391,⟨sg32390,True.intro,True.intro⟩,True.intro⟩,⟨sg32394,⟨sg32393,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32398,⟨sg32397,⟨sg32396,True.intro,True.intro⟩,True.intro⟩,⟨sg32399,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_33All : degreeTree62_33.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32378,degreeTree62_31All,degreeTree62_32All⟩

lemma degreeTree62_34All : degreeTree62_34.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32411,⟨sg32406,⟨sg32403,⟨sg32402,⟨sg32401,True.intro,True.intro⟩,True.intro⟩,⟨sg32405,⟨sg32404,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32409,⟨sg32408,⟨sg32407,True.intro,True.intro⟩,True.intro⟩,⟨sg32410,True.intro,True.intro⟩⟩⟩,⟨sg32417,⟨sg32414,⟨sg32413,⟨sg32412,True.intro,True.intro⟩,True.intro⟩,⟨sg32416,⟨sg32415,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32420,⟨sg32419,⟨sg32418,True.intro,True.intro⟩,True.intro⟩,⟨sg32421,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_35All : degreeTree62_35.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32433,⟨sg32428,⟨sg32425,⟨sg32424,⟨sg32423,True.intro,True.intro⟩,True.intro⟩,⟨sg32427,⟨sg32426,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32431,⟨sg32430,⟨sg32429,True.intro,True.intro⟩,True.intro⟩,⟨sg32432,True.intro,True.intro⟩⟩⟩,⟨sg32439,⟨sg32436,⟨sg32435,⟨sg32434,True.intro,True.intro⟩,True.intro⟩,⟨sg32438,⟨sg32437,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32442,⟨sg32441,⟨sg32440,True.intro,True.intro⟩,True.intro⟩,⟨sg32443,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_36All : degreeTree62_36.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32422,degreeTree62_34All,degreeTree62_35All⟩

lemma degreeTree62_37All : degreeTree62_37.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32400,degreeTree62_33All,degreeTree62_36All⟩

lemma degreeTree62_38All : degreeTree62_38.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32455,⟨sg32450,⟨sg32447,⟨sg32446,⟨sg32445,True.intro,True.intro⟩,True.intro⟩,⟨sg32449,⟨sg32448,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32453,⟨sg32452,⟨sg32451,True.intro,True.intro⟩,True.intro⟩,⟨sg32454,True.intro,True.intro⟩⟩⟩,⟨sg32461,⟨sg32458,⟨sg32457,⟨sg32456,True.intro,True.intro⟩,True.intro⟩,⟨sg32460,⟨sg32459,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32464,⟨sg32463,⟨sg32462,True.intro,True.intro⟩,True.intro⟩,⟨sg32465,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_39All : degreeTree62_39.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32477,⟨sg32472,⟨sg32469,⟨sg32468,⟨sg32467,True.intro,True.intro⟩,True.intro⟩,⟨sg32471,⟨sg32470,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32475,⟨sg32474,⟨sg32473,True.intro,True.intro⟩,True.intro⟩,⟨sg32476,True.intro,True.intro⟩⟩⟩,⟨sg32483,⟨sg32480,⟨sg32479,⟨sg32478,True.intro,True.intro⟩,True.intro⟩,⟨sg32482,⟨sg32481,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32486,⟨sg32485,⟨sg32484,True.intro,True.intro⟩,True.intro⟩,⟨sg32487,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_40All : degreeTree62_40.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32466,degreeTree62_38All,degreeTree62_39All⟩

lemma degreeTree62_41All : degreeTree62_41.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32499,⟨sg32494,⟨sg32491,⟨sg32490,⟨sg32489,True.intro,True.intro⟩,True.intro⟩,⟨sg32493,⟨sg32492,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32497,⟨sg32496,⟨sg32495,True.intro,True.intro⟩,True.intro⟩,⟨sg32498,True.intro,True.intro⟩⟩⟩,⟨sg32505,⟨sg32502,⟨sg32501,⟨sg32500,True.intro,True.intro⟩,True.intro⟩,⟨sg32504,⟨sg32503,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32508,⟨sg32507,⟨sg32506,True.intro,True.intro⟩,True.intro⟩,⟨sg32509,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_42All : degreeTree62_42.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32521,⟨sg32516,⟨sg32513,⟨sg32512,⟨sg32511,True.intro,True.intro⟩,True.intro⟩,⟨sg32515,⟨sg32514,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32519,⟨sg32518,⟨sg32517,True.intro,True.intro⟩,True.intro⟩,⟨sg32520,True.intro,True.intro⟩⟩⟩,⟨sg32527,⟨sg32524,⟨sg32523,⟨sg32522,True.intro,True.intro⟩,True.intro⟩,⟨sg32526,⟨sg32525,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32530,⟨sg32529,⟨sg32528,True.intro,True.intro⟩,True.intro⟩,⟨sg32531,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_43All : degreeTree62_43.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32510,degreeTree62_41All,degreeTree62_42All⟩

lemma degreeTree62_44All : degreeTree62_44.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32488,degreeTree62_40All,degreeTree62_43All⟩

lemma degreeTree62_45All : degreeTree62_45.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32444,degreeTree62_37All,degreeTree62_44All⟩

lemma degreeTree62_46All : degreeTree62_46.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32543,⟨sg32538,⟨sg32535,⟨sg32534,⟨sg32533,True.intro,True.intro⟩,True.intro⟩,⟨sg32537,⟨sg32536,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32541,⟨sg32540,⟨sg32539,True.intro,True.intro⟩,True.intro⟩,⟨sg32542,True.intro,True.intro⟩⟩⟩,⟨sg32549,⟨sg32546,⟨sg32545,⟨sg32544,True.intro,True.intro⟩,True.intro⟩,⟨sg32548,⟨sg32547,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32552,⟨sg32551,⟨sg32550,True.intro,True.intro⟩,True.intro⟩,⟨sg32553,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_47All : degreeTree62_47.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32565,⟨sg32560,⟨sg32557,⟨sg32556,⟨sg32555,True.intro,True.intro⟩,True.intro⟩,⟨sg32559,⟨sg32558,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32563,⟨sg32562,⟨sg32561,True.intro,True.intro⟩,True.intro⟩,⟨sg32564,True.intro,True.intro⟩⟩⟩,⟨sg32571,⟨sg32568,⟨sg32567,⟨sg32566,True.intro,True.intro⟩,True.intro⟩,⟨sg32570,⟨sg32569,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32574,⟨sg32573,⟨sg32572,True.intro,True.intro⟩,True.intro⟩,⟨sg32575,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_48All : degreeTree62_48.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32554,degreeTree62_46All,degreeTree62_47All⟩

lemma degreeTree62_49All : degreeTree62_49.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32587,⟨sg32582,⟨sg32579,⟨sg32578,⟨sg32577,True.intro,True.intro⟩,True.intro⟩,⟨sg32581,⟨sg32580,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32585,⟨sg32584,⟨sg32583,True.intro,True.intro⟩,True.intro⟩,⟨sg32586,True.intro,True.intro⟩⟩⟩,⟨sg32593,⟨sg32590,⟨sg32589,⟨sg32588,True.intro,True.intro⟩,True.intro⟩,⟨sg32592,⟨sg32591,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32596,⟨sg32595,⟨sg32594,True.intro,True.intro⟩,True.intro⟩,⟨sg32597,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_50All : degreeTree62_50.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32609,⟨sg32604,⟨sg32601,⟨sg32600,⟨sg32599,True.intro,True.intro⟩,True.intro⟩,⟨sg32603,⟨sg32602,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32607,⟨sg32606,⟨sg32605,True.intro,True.intro⟩,True.intro⟩,⟨sg32608,True.intro,True.intro⟩⟩⟩,⟨sg32615,⟨sg32612,⟨sg32611,⟨sg32610,True.intro,True.intro⟩,True.intro⟩,⟨sg32614,⟨sg32613,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32618,⟨sg32617,⟨sg32616,True.intro,True.intro⟩,True.intro⟩,⟨sg32619,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_51All : degreeTree62_51.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32598,degreeTree62_49All,degreeTree62_50All⟩

lemma degreeTree62_52All : degreeTree62_52.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32576,degreeTree62_48All,degreeTree62_51All⟩

lemma degreeTree62_53All : degreeTree62_53.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32631,⟨sg32626,⟨sg32623,⟨sg32622,⟨sg32621,True.intro,True.intro⟩,True.intro⟩,⟨sg32625,⟨sg32624,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32629,⟨sg32628,⟨sg32627,True.intro,True.intro⟩,True.intro⟩,⟨sg32630,True.intro,True.intro⟩⟩⟩,⟨sg32637,⟨sg32634,⟨sg32633,⟨sg32632,True.intro,True.intro⟩,True.intro⟩,⟨sg32636,⟨sg32635,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32640,⟨sg32639,⟨sg32638,True.intro,True.intro⟩,True.intro⟩,⟨sg32641,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_54All : degreeTree62_54.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32653,⟨sg32648,⟨sg32645,⟨sg32644,⟨sg32643,True.intro,True.intro⟩,True.intro⟩,⟨sg32647,⟨sg32646,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32651,⟨sg32650,⟨sg32649,True.intro,True.intro⟩,True.intro⟩,⟨sg32652,True.intro,True.intro⟩⟩⟩,⟨sg32659,⟨sg32656,⟨sg32655,⟨sg32654,True.intro,True.intro⟩,True.intro⟩,⟨sg32658,⟨sg32657,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32662,⟨sg32661,⟨sg32660,True.intro,True.intro⟩,True.intro⟩,⟨sg32663,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_55All : degreeTree62_55.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32642,degreeTree62_53All,degreeTree62_54All⟩

lemma degreeTree62_56All : degreeTree62_56.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32675,⟨sg32670,⟨sg32667,⟨sg32666,⟨sg32665,True.intro,True.intro⟩,True.intro⟩,⟨sg32669,⟨sg32668,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32673,⟨sg32672,⟨sg32671,True.intro,True.intro⟩,True.intro⟩,⟨sg32674,True.intro,True.intro⟩⟩⟩,⟨sg32681,⟨sg32678,⟨sg32677,⟨sg32676,True.intro,True.intro⟩,True.intro⟩,⟨sg32680,⟨sg32679,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32684,⟨sg32683,⟨sg32682,True.intro,True.intro⟩,True.intro⟩,⟨sg32685,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_57All : degreeTree62_57.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32697,⟨sg32692,⟨sg32689,⟨sg32688,⟨sg32687,True.intro,True.intro⟩,True.intro⟩,⟨sg32691,⟨sg32690,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32695,⟨sg32694,⟨sg32693,True.intro,True.intro⟩,True.intro⟩,⟨sg32696,True.intro,True.intro⟩⟩⟩,⟨sg32702,⟨sg32700,⟨sg32699,⟨sg32698,True.intro,True.intro⟩,True.intro⟩,⟨sg32701,True.intro,True.intro⟩⟩,⟨sg32705,⟨sg32704,⟨sg32703,True.intro,True.intro⟩,True.intro⟩,⟨sg32706,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_58All : degreeTree62_58.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32686,degreeTree62_56All,degreeTree62_57All⟩

lemma degreeTree62_59All : degreeTree62_59.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32664,degreeTree62_55All,degreeTree62_58All⟩

lemma degreeTree62_60All : degreeTree62_60.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32620,degreeTree62_52All,degreeTree62_59All⟩

lemma degreeTree62_61All : degreeTree62_61.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32532,degreeTree62_45All,degreeTree62_60All⟩

lemma degreeTree62_62All : degreeTree62_62.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32356,degreeTree62_30All,degreeTree62_61All⟩

lemma degreeTree62_63All : degreeTree62_63.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32718,⟨sg32713,⟨sg32710,⟨sg32709,⟨sg32708,True.intro,True.intro⟩,True.intro⟩,⟨sg32712,⟨sg32711,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32716,⟨sg32715,⟨sg32714,True.intro,True.intro⟩,True.intro⟩,⟨sg32717,True.intro,True.intro⟩⟩⟩,⟨sg32724,⟨sg32721,⟨sg32720,⟨sg32719,True.intro,True.intro⟩,True.intro⟩,⟨sg32723,⟨sg32722,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32727,⟨sg32726,⟨sg32725,True.intro,True.intro⟩,True.intro⟩,⟨sg32728,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_64All : degreeTree62_64.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32740,⟨sg32735,⟨sg32732,⟨sg32731,⟨sg32730,True.intro,True.intro⟩,True.intro⟩,⟨sg32734,⟨sg32733,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32738,⟨sg32737,⟨sg32736,True.intro,True.intro⟩,True.intro⟩,⟨sg32739,True.intro,True.intro⟩⟩⟩,⟨sg32746,⟨sg32743,⟨sg32742,⟨sg32741,True.intro,True.intro⟩,True.intro⟩,⟨sg32745,⟨sg32744,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32749,⟨sg32748,⟨sg32747,True.intro,True.intro⟩,True.intro⟩,⟨sg32750,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_65All : degreeTree62_65.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32729,degreeTree62_63All,degreeTree62_64All⟩

lemma degreeTree62_66All : degreeTree62_66.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32762,⟨sg32757,⟨sg32754,⟨sg32753,⟨sg32752,True.intro,True.intro⟩,True.intro⟩,⟨sg32756,⟨sg32755,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32760,⟨sg32759,⟨sg32758,True.intro,True.intro⟩,True.intro⟩,⟨sg32761,True.intro,True.intro⟩⟩⟩,⟨sg32768,⟨sg32765,⟨sg32764,⟨sg32763,True.intro,True.intro⟩,True.intro⟩,⟨sg32767,⟨sg32766,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32771,⟨sg32770,⟨sg32769,True.intro,True.intro⟩,True.intro⟩,⟨sg32772,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_67All : degreeTree62_67.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32784,⟨sg32779,⟨sg32776,⟨sg32775,⟨sg32774,True.intro,True.intro⟩,True.intro⟩,⟨sg32778,⟨sg32777,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32782,⟨sg32781,⟨sg32780,True.intro,True.intro⟩,True.intro⟩,⟨sg32783,True.intro,True.intro⟩⟩⟩,⟨sg32790,⟨sg32787,⟨sg32786,⟨sg32785,True.intro,True.intro⟩,True.intro⟩,⟨sg32789,⟨sg32788,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32793,⟨sg32792,⟨sg32791,True.intro,True.intro⟩,True.intro⟩,⟨sg32794,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_68All : degreeTree62_68.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32773,degreeTree62_66All,degreeTree62_67All⟩

lemma degreeTree62_69All : degreeTree62_69.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32751,degreeTree62_65All,degreeTree62_68All⟩

lemma degreeTree62_70All : degreeTree62_70.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32806,⟨sg32801,⟨sg32798,⟨sg32797,⟨sg32796,True.intro,True.intro⟩,True.intro⟩,⟨sg32800,⟨sg32799,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32804,⟨sg32803,⟨sg32802,True.intro,True.intro⟩,True.intro⟩,⟨sg32805,True.intro,True.intro⟩⟩⟩,⟨sg32812,⟨sg32809,⟨sg32808,⟨sg32807,True.intro,True.intro⟩,True.intro⟩,⟨sg32811,⟨sg32810,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32815,⟨sg32814,⟨sg32813,True.intro,True.intro⟩,True.intro⟩,⟨sg32816,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_71All : degreeTree62_71.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32828,⟨sg32823,⟨sg32820,⟨sg32819,⟨sg32818,True.intro,True.intro⟩,True.intro⟩,⟨sg32822,⟨sg32821,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32826,⟨sg32825,⟨sg32824,True.intro,True.intro⟩,True.intro⟩,⟨sg32827,True.intro,True.intro⟩⟩⟩,⟨sg32834,⟨sg32831,⟨sg32830,⟨sg32829,True.intro,True.intro⟩,True.intro⟩,⟨sg32833,⟨sg32832,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32837,⟨sg32836,⟨sg32835,True.intro,True.intro⟩,True.intro⟩,⟨sg32838,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_72All : degreeTree62_72.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32817,degreeTree62_70All,degreeTree62_71All⟩

lemma degreeTree62_73All : degreeTree62_73.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32850,⟨sg32845,⟨sg32842,⟨sg32841,⟨sg32840,True.intro,True.intro⟩,True.intro⟩,⟨sg32844,⟨sg32843,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32848,⟨sg32847,⟨sg32846,True.intro,True.intro⟩,True.intro⟩,⟨sg32849,True.intro,True.intro⟩⟩⟩,⟨sg32856,⟨sg32853,⟨sg32852,⟨sg32851,True.intro,True.intro⟩,True.intro⟩,⟨sg32855,⟨sg32854,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32859,⟨sg32858,⟨sg32857,True.intro,True.intro⟩,True.intro⟩,⟨sg32860,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_74All : degreeTree62_74.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32872,⟨sg32867,⟨sg32864,⟨sg32863,⟨sg32862,True.intro,True.intro⟩,True.intro⟩,⟨sg32866,⟨sg32865,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32870,⟨sg32869,⟨sg32868,True.intro,True.intro⟩,True.intro⟩,⟨sg32871,True.intro,True.intro⟩⟩⟩,⟨sg32878,⟨sg32875,⟨sg32874,⟨sg32873,True.intro,True.intro⟩,True.intro⟩,⟨sg32877,⟨sg32876,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32881,⟨sg32880,⟨sg32879,True.intro,True.intro⟩,True.intro⟩,⟨sg32882,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_75All : degreeTree62_75.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32861,degreeTree62_73All,degreeTree62_74All⟩

lemma degreeTree62_76All : degreeTree62_76.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32839,degreeTree62_72All,degreeTree62_75All⟩

lemma degreeTree62_77All : degreeTree62_77.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32795,degreeTree62_69All,degreeTree62_76All⟩

lemma degreeTree62_78All : degreeTree62_78.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32894,⟨sg32889,⟨sg32886,⟨sg32885,⟨sg32884,True.intro,True.intro⟩,True.intro⟩,⟨sg32888,⟨sg32887,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32892,⟨sg32891,⟨sg32890,True.intro,True.intro⟩,True.intro⟩,⟨sg32893,True.intro,True.intro⟩⟩⟩,⟨sg32900,⟨sg32897,⟨sg32896,⟨sg32895,True.intro,True.intro⟩,True.intro⟩,⟨sg32899,⟨sg32898,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32903,⟨sg32902,⟨sg32901,True.intro,True.intro⟩,True.intro⟩,⟨sg32904,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_79All : degreeTree62_79.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32916,⟨sg32911,⟨sg32908,⟨sg32907,⟨sg32906,True.intro,True.intro⟩,True.intro⟩,⟨sg32910,⟨sg32909,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32914,⟨sg32913,⟨sg32912,True.intro,True.intro⟩,True.intro⟩,⟨sg32915,True.intro,True.intro⟩⟩⟩,⟨sg32922,⟨sg32919,⟨sg32918,⟨sg32917,True.intro,True.intro⟩,True.intro⟩,⟨sg32921,⟨sg32920,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32925,⟨sg32924,⟨sg32923,True.intro,True.intro⟩,True.intro⟩,⟨sg32926,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_80All : degreeTree62_80.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32905,degreeTree62_78All,degreeTree62_79All⟩

lemma degreeTree62_81All : degreeTree62_81.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32938,⟨sg32933,⟨sg32930,⟨sg32929,⟨sg32928,True.intro,True.intro⟩,True.intro⟩,⟨sg32932,⟨sg32931,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32936,⟨sg32935,⟨sg32934,True.intro,True.intro⟩,True.intro⟩,⟨sg32937,True.intro,True.intro⟩⟩⟩,⟨sg32944,⟨sg32941,⟨sg32940,⟨sg32939,True.intro,True.intro⟩,True.intro⟩,⟨sg32943,⟨sg32942,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32947,⟨sg32946,⟨sg32945,True.intro,True.intro⟩,True.intro⟩,⟨sg32948,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_82All : degreeTree62_82.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32960,⟨sg32955,⟨sg32952,⟨sg32951,⟨sg32950,True.intro,True.intro⟩,True.intro⟩,⟨sg32954,⟨sg32953,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32958,⟨sg32957,⟨sg32956,True.intro,True.intro⟩,True.intro⟩,⟨sg32959,True.intro,True.intro⟩⟩⟩,⟨sg32966,⟨sg32963,⟨sg32962,⟨sg32961,True.intro,True.intro⟩,True.intro⟩,⟨sg32965,⟨sg32964,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32969,⟨sg32968,⟨sg32967,True.intro,True.intro⟩,True.intro⟩,⟨sg32970,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_83All : degreeTree62_83.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32949,degreeTree62_81All,degreeTree62_82All⟩

lemma degreeTree62_84All : degreeTree62_84.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32927,degreeTree62_80All,degreeTree62_83All⟩

lemma degreeTree62_85All : degreeTree62_85.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32982,⟨sg32977,⟨sg32974,⟨sg32973,⟨sg32972,True.intro,True.intro⟩,True.intro⟩,⟨sg32976,⟨sg32975,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32980,⟨sg32979,⟨sg32978,True.intro,True.intro⟩,True.intro⟩,⟨sg32981,True.intro,True.intro⟩⟩⟩,⟨sg32988,⟨sg32985,⟨sg32984,⟨sg32983,True.intro,True.intro⟩,True.intro⟩,⟨sg32987,⟨sg32986,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg32991,⟨sg32990,⟨sg32989,True.intro,True.intro⟩,True.intro⟩,⟨sg32992,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_86All : degreeTree62_86.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33004,⟨sg32999,⟨sg32996,⟨sg32995,⟨sg32994,True.intro,True.intro⟩,True.intro⟩,⟨sg32998,⟨sg32997,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33002,⟨sg33001,⟨sg33000,True.intro,True.intro⟩,True.intro⟩,⟨sg33003,True.intro,True.intro⟩⟩⟩,⟨sg33010,⟨sg33007,⟨sg33006,⟨sg33005,True.intro,True.intro⟩,True.intro⟩,⟨sg33009,⟨sg33008,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33013,⟨sg33012,⟨sg33011,True.intro,True.intro⟩,True.intro⟩,⟨sg33014,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_87All : degreeTree62_87.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32993,degreeTree62_85All,degreeTree62_86All⟩

lemma degreeTree62_88All : degreeTree62_88.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33026,⟨sg33021,⟨sg33018,⟨sg33017,⟨sg33016,True.intro,True.intro⟩,True.intro⟩,⟨sg33020,⟨sg33019,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33024,⟨sg33023,⟨sg33022,True.intro,True.intro⟩,True.intro⟩,⟨sg33025,True.intro,True.intro⟩⟩⟩,⟨sg33032,⟨sg33029,⟨sg33028,⟨sg33027,True.intro,True.intro⟩,True.intro⟩,⟨sg33031,⟨sg33030,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33035,⟨sg33034,⟨sg33033,True.intro,True.intro⟩,True.intro⟩,⟨sg33036,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_89All : degreeTree62_89.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33048,⟨sg33043,⟨sg33040,⟨sg33039,⟨sg33038,True.intro,True.intro⟩,True.intro⟩,⟨sg33042,⟨sg33041,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33046,⟨sg33045,⟨sg33044,True.intro,True.intro⟩,True.intro⟩,⟨sg33047,True.intro,True.intro⟩⟩⟩,⟨sg33053,⟨sg33051,⟨sg33050,⟨sg33049,True.intro,True.intro⟩,True.intro⟩,⟨sg33052,True.intro,True.intro⟩⟩,⟨sg33056,⟨sg33055,⟨sg33054,True.intro,True.intro⟩,True.intro⟩,⟨sg33057,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_90All : degreeTree62_90.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33037,degreeTree62_88All,degreeTree62_89All⟩

lemma degreeTree62_91All : degreeTree62_91.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33015,degreeTree62_87All,degreeTree62_90All⟩

lemma degreeTree62_92All : degreeTree62_92.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32971,degreeTree62_84All,degreeTree62_91All⟩

lemma degreeTree62_93All : degreeTree62_93.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32883,degreeTree62_77All,degreeTree62_92All⟩

lemma degreeTree62_94All : degreeTree62_94.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33069,⟨sg33064,⟨sg33061,⟨sg33060,⟨sg33059,True.intro,True.intro⟩,True.intro⟩,⟨sg33063,⟨sg33062,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33067,⟨sg33066,⟨sg33065,True.intro,True.intro⟩,True.intro⟩,⟨sg33068,True.intro,True.intro⟩⟩⟩,⟨sg33075,⟨sg33072,⟨sg33071,⟨sg33070,True.intro,True.intro⟩,True.intro⟩,⟨sg33074,⟨sg33073,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33078,⟨sg33077,⟨sg33076,True.intro,True.intro⟩,True.intro⟩,⟨sg33079,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_95All : degreeTree62_95.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33091,⟨sg33086,⟨sg33083,⟨sg33082,⟨sg33081,True.intro,True.intro⟩,True.intro⟩,⟨sg33085,⟨sg33084,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33089,⟨sg33088,⟨sg33087,True.intro,True.intro⟩,True.intro⟩,⟨sg33090,True.intro,True.intro⟩⟩⟩,⟨sg33097,⟨sg33094,⟨sg33093,⟨sg33092,True.intro,True.intro⟩,True.intro⟩,⟨sg33096,⟨sg33095,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33100,⟨sg33099,⟨sg33098,True.intro,True.intro⟩,True.intro⟩,⟨sg33101,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_96All : degreeTree62_96.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33080,degreeTree62_94All,degreeTree62_95All⟩

lemma degreeTree62_97All : degreeTree62_97.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33113,⟨sg33108,⟨sg33105,⟨sg33104,⟨sg33103,True.intro,True.intro⟩,True.intro⟩,⟨sg33107,⟨sg33106,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33111,⟨sg33110,⟨sg33109,True.intro,True.intro⟩,True.intro⟩,⟨sg33112,True.intro,True.intro⟩⟩⟩,⟨sg33119,⟨sg33116,⟨sg33115,⟨sg33114,True.intro,True.intro⟩,True.intro⟩,⟨sg33118,⟨sg33117,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33122,⟨sg33121,⟨sg33120,True.intro,True.intro⟩,True.intro⟩,⟨sg33123,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_98All : degreeTree62_98.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33135,⟨sg33130,⟨sg33127,⟨sg33126,⟨sg33125,True.intro,True.intro⟩,True.intro⟩,⟨sg33129,⟨sg33128,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33133,⟨sg33132,⟨sg33131,True.intro,True.intro⟩,True.intro⟩,⟨sg33134,True.intro,True.intro⟩⟩⟩,⟨sg33141,⟨sg33138,⟨sg33137,⟨sg33136,True.intro,True.intro⟩,True.intro⟩,⟨sg33140,⟨sg33139,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33144,⟨sg33143,⟨sg33142,True.intro,True.intro⟩,True.intro⟩,⟨sg33145,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_99All : degreeTree62_99.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33124,degreeTree62_97All,degreeTree62_98All⟩

lemma degreeTree62_100All : degreeTree62_100.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33102,degreeTree62_96All,degreeTree62_99All⟩

lemma degreeTree62_101All : degreeTree62_101.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33157,⟨sg33152,⟨sg33149,⟨sg33148,⟨sg33147,True.intro,True.intro⟩,True.intro⟩,⟨sg33151,⟨sg33150,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33155,⟨sg33154,⟨sg33153,True.intro,True.intro⟩,True.intro⟩,⟨sg33156,True.intro,True.intro⟩⟩⟩,⟨sg33163,⟨sg33160,⟨sg33159,⟨sg33158,True.intro,True.intro⟩,True.intro⟩,⟨sg33162,⟨sg33161,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33166,⟨sg33165,⟨sg33164,True.intro,True.intro⟩,True.intro⟩,⟨sg33167,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_102All : degreeTree62_102.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33179,⟨sg33174,⟨sg33171,⟨sg33170,⟨sg33169,True.intro,True.intro⟩,True.intro⟩,⟨sg33173,⟨sg33172,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33177,⟨sg33176,⟨sg33175,True.intro,True.intro⟩,True.intro⟩,⟨sg33178,True.intro,True.intro⟩⟩⟩,⟨sg33185,⟨sg33182,⟨sg33181,⟨sg33180,True.intro,True.intro⟩,True.intro⟩,⟨sg33184,⟨sg33183,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33188,⟨sg33187,⟨sg33186,True.intro,True.intro⟩,True.intro⟩,⟨sg33189,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_103All : degreeTree62_103.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33168,degreeTree62_101All,degreeTree62_102All⟩

lemma degreeTree62_104All : degreeTree62_104.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33201,⟨sg33196,⟨sg33193,⟨sg33192,⟨sg33191,True.intro,True.intro⟩,True.intro⟩,⟨sg33195,⟨sg33194,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33199,⟨sg33198,⟨sg33197,True.intro,True.intro⟩,True.intro⟩,⟨sg33200,True.intro,True.intro⟩⟩⟩,⟨sg33207,⟨sg33204,⟨sg33203,⟨sg33202,True.intro,True.intro⟩,True.intro⟩,⟨sg33206,⟨sg33205,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33210,⟨sg33209,⟨sg33208,True.intro,True.intro⟩,True.intro⟩,⟨sg33211,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_105All : degreeTree62_105.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33223,⟨sg33218,⟨sg33215,⟨sg33214,⟨sg33213,True.intro,True.intro⟩,True.intro⟩,⟨sg33217,⟨sg33216,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33221,⟨sg33220,⟨sg33219,True.intro,True.intro⟩,True.intro⟩,⟨sg33222,True.intro,True.intro⟩⟩⟩,⟨sg33229,⟨sg33226,⟨sg33225,⟨sg33224,True.intro,True.intro⟩,True.intro⟩,⟨sg33228,⟨sg33227,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33232,⟨sg33231,⟨sg33230,True.intro,True.intro⟩,True.intro⟩,⟨sg33233,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_106All : degreeTree62_106.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33212,degreeTree62_104All,degreeTree62_105All⟩

lemma degreeTree62_107All : degreeTree62_107.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33190,degreeTree62_103All,degreeTree62_106All⟩

lemma degreeTree62_108All : degreeTree62_108.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33146,degreeTree62_100All,degreeTree62_107All⟩

lemma degreeTree62_109All : degreeTree62_109.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33245,⟨sg33240,⟨sg33237,⟨sg33236,⟨sg33235,True.intro,True.intro⟩,True.intro⟩,⟨sg33239,⟨sg33238,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33243,⟨sg33242,⟨sg33241,True.intro,True.intro⟩,True.intro⟩,⟨sg33244,True.intro,True.intro⟩⟩⟩,⟨sg33251,⟨sg33248,⟨sg33247,⟨sg33246,True.intro,True.intro⟩,True.intro⟩,⟨sg33250,⟨sg33249,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33254,⟨sg33253,⟨sg33252,True.intro,True.intro⟩,True.intro⟩,⟨sg33255,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_110All : degreeTree62_110.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33267,⟨sg33262,⟨sg33259,⟨sg33258,⟨sg33257,True.intro,True.intro⟩,True.intro⟩,⟨sg33261,⟨sg33260,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33265,⟨sg33264,⟨sg33263,True.intro,True.intro⟩,True.intro⟩,⟨sg33266,True.intro,True.intro⟩⟩⟩,⟨sg33273,⟨sg33270,⟨sg33269,⟨sg33268,True.intro,True.intro⟩,True.intro⟩,⟨sg33272,⟨sg33271,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33276,⟨sg33275,⟨sg33274,True.intro,True.intro⟩,True.intro⟩,⟨sg33277,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_111All : degreeTree62_111.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33256,degreeTree62_109All,degreeTree62_110All⟩

lemma degreeTree62_112All : degreeTree62_112.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33289,⟨sg33284,⟨sg33281,⟨sg33280,⟨sg33279,True.intro,True.intro⟩,True.intro⟩,⟨sg33283,⟨sg33282,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33287,⟨sg33286,⟨sg33285,True.intro,True.intro⟩,True.intro⟩,⟨sg33288,True.intro,True.intro⟩⟩⟩,⟨sg33295,⟨sg33292,⟨sg33291,⟨sg33290,True.intro,True.intro⟩,True.intro⟩,⟨sg33294,⟨sg33293,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33298,⟨sg33297,⟨sg33296,True.intro,True.intro⟩,True.intro⟩,⟨sg33299,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_113All : degreeTree62_113.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33311,⟨sg33306,⟨sg33303,⟨sg33302,⟨sg33301,True.intro,True.intro⟩,True.intro⟩,⟨sg33305,⟨sg33304,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33309,⟨sg33308,⟨sg33307,True.intro,True.intro⟩,True.intro⟩,⟨sg33310,True.intro,True.intro⟩⟩⟩,⟨sg33317,⟨sg33314,⟨sg33313,⟨sg33312,True.intro,True.intro⟩,True.intro⟩,⟨sg33316,⟨sg33315,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33320,⟨sg33319,⟨sg33318,True.intro,True.intro⟩,True.intro⟩,⟨sg33321,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_114All : degreeTree62_114.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33300,degreeTree62_112All,degreeTree62_113All⟩

lemma degreeTree62_115All : degreeTree62_115.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33278,degreeTree62_111All,degreeTree62_114All⟩

lemma degreeTree62_116All : degreeTree62_116.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33333,⟨sg33328,⟨sg33325,⟨sg33324,⟨sg33323,True.intro,True.intro⟩,True.intro⟩,⟨sg33327,⟨sg33326,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33331,⟨sg33330,⟨sg33329,True.intro,True.intro⟩,True.intro⟩,⟨sg33332,True.intro,True.intro⟩⟩⟩,⟨sg33339,⟨sg33336,⟨sg33335,⟨sg33334,True.intro,True.intro⟩,True.intro⟩,⟨sg33338,⟨sg33337,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33342,⟨sg33341,⟨sg33340,True.intro,True.intro⟩,True.intro⟩,⟨sg33343,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_117All : degreeTree62_117.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33355,⟨sg33350,⟨sg33347,⟨sg33346,⟨sg33345,True.intro,True.intro⟩,True.intro⟩,⟨sg33349,⟨sg33348,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33353,⟨sg33352,⟨sg33351,True.intro,True.intro⟩,True.intro⟩,⟨sg33354,True.intro,True.intro⟩⟩⟩,⟨sg33361,⟨sg33358,⟨sg33357,⟨sg33356,True.intro,True.intro⟩,True.intro⟩,⟨sg33360,⟨sg33359,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33364,⟨sg33363,⟨sg33362,True.intro,True.intro⟩,True.intro⟩,⟨sg33365,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_118All : degreeTree62_118.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33344,degreeTree62_116All,degreeTree62_117All⟩

lemma degreeTree62_119All : degreeTree62_119.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33377,⟨sg33372,⟨sg33369,⟨sg33368,⟨sg33367,True.intro,True.intro⟩,True.intro⟩,⟨sg33371,⟨sg33370,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33375,⟨sg33374,⟨sg33373,True.intro,True.intro⟩,True.intro⟩,⟨sg33376,True.intro,True.intro⟩⟩⟩,⟨sg33383,⟨sg33380,⟨sg33379,⟨sg33378,True.intro,True.intro⟩,True.intro⟩,⟨sg33382,⟨sg33381,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33386,⟨sg33385,⟨sg33384,True.intro,True.intro⟩,True.intro⟩,⟨sg33387,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_120All : degreeTree62_120.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33399,⟨sg33394,⟨sg33391,⟨sg33390,⟨sg33389,True.intro,True.intro⟩,True.intro⟩,⟨sg33393,⟨sg33392,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33397,⟨sg33396,⟨sg33395,True.intro,True.intro⟩,True.intro⟩,⟨sg33398,True.intro,True.intro⟩⟩⟩,⟨sg33404,⟨sg33402,⟨sg33401,⟨sg33400,True.intro,True.intro⟩,True.intro⟩,⟨sg33403,True.intro,True.intro⟩⟩,⟨sg33407,⟨sg33406,⟨sg33405,True.intro,True.intro⟩,True.intro⟩,⟨sg33408,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_121All : degreeTree62_121.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33388,degreeTree62_119All,degreeTree62_120All⟩

lemma degreeTree62_122All : degreeTree62_122.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33366,degreeTree62_118All,degreeTree62_121All⟩

lemma degreeTree62_123All : degreeTree62_123.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33322,degreeTree62_115All,degreeTree62_122All⟩

lemma degreeTree62_124All : degreeTree62_124.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33234,degreeTree62_108All,degreeTree62_123All⟩

lemma degreeTree62_125All : degreeTree62_125.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33058,degreeTree62_93All,degreeTree62_124All⟩

lemma degreeTree62_126All : degreeTree62_126.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg32707,degreeTree62_62All,degreeTree62_125All⟩

lemma degreeTree62_127All : degreeTree62_127.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33420,⟨sg33415,⟨sg33412,⟨sg33411,⟨sg33410,True.intro,True.intro⟩,True.intro⟩,⟨sg33414,⟨sg33413,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33418,⟨sg33417,⟨sg33416,True.intro,True.intro⟩,True.intro⟩,⟨sg33419,True.intro,True.intro⟩⟩⟩,⟨sg33426,⟨sg33423,⟨sg33422,⟨sg33421,True.intro,True.intro⟩,True.intro⟩,⟨sg33425,⟨sg33424,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33429,⟨sg33428,⟨sg33427,True.intro,True.intro⟩,True.intro⟩,⟨sg33430,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_128All : degreeTree62_128.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33442,⟨sg33437,⟨sg33434,⟨sg33433,⟨sg33432,True.intro,True.intro⟩,True.intro⟩,⟨sg33436,⟨sg33435,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33440,⟨sg33439,⟨sg33438,True.intro,True.intro⟩,True.intro⟩,⟨sg33441,True.intro,True.intro⟩⟩⟩,⟨sg33448,⟨sg33445,⟨sg33444,⟨sg33443,True.intro,True.intro⟩,True.intro⟩,⟨sg33447,⟨sg33446,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33451,⟨sg33450,⟨sg33449,True.intro,True.intro⟩,True.intro⟩,⟨sg33452,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_129All : degreeTree62_129.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33431,degreeTree62_127All,degreeTree62_128All⟩

lemma degreeTree62_130All : degreeTree62_130.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33464,⟨sg33459,⟨sg33456,⟨sg33455,⟨sg33454,True.intro,True.intro⟩,True.intro⟩,⟨sg33458,⟨sg33457,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33462,⟨sg33461,⟨sg33460,True.intro,True.intro⟩,True.intro⟩,⟨sg33463,True.intro,True.intro⟩⟩⟩,⟨sg33470,⟨sg33467,⟨sg33466,⟨sg33465,True.intro,True.intro⟩,True.intro⟩,⟨sg33469,⟨sg33468,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33473,⟨sg33472,⟨sg33471,True.intro,True.intro⟩,True.intro⟩,⟨sg33474,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_131All : degreeTree62_131.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33486,⟨sg33481,⟨sg33478,⟨sg33477,⟨sg33476,True.intro,True.intro⟩,True.intro⟩,⟨sg33480,⟨sg33479,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33484,⟨sg33483,⟨sg33482,True.intro,True.intro⟩,True.intro⟩,⟨sg33485,True.intro,True.intro⟩⟩⟩,⟨sg33492,⟨sg33489,⟨sg33488,⟨sg33487,True.intro,True.intro⟩,True.intro⟩,⟨sg33491,⟨sg33490,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33495,⟨sg33494,⟨sg33493,True.intro,True.intro⟩,True.intro⟩,⟨sg33496,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_132All : degreeTree62_132.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33475,degreeTree62_130All,degreeTree62_131All⟩

lemma degreeTree62_133All : degreeTree62_133.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33453,degreeTree62_129All,degreeTree62_132All⟩

lemma degreeTree62_134All : degreeTree62_134.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33508,⟨sg33503,⟨sg33500,⟨sg33499,⟨sg33498,True.intro,True.intro⟩,True.intro⟩,⟨sg33502,⟨sg33501,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33506,⟨sg33505,⟨sg33504,True.intro,True.intro⟩,True.intro⟩,⟨sg33507,True.intro,True.intro⟩⟩⟩,⟨sg33514,⟨sg33511,⟨sg33510,⟨sg33509,True.intro,True.intro⟩,True.intro⟩,⟨sg33513,⟨sg33512,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33517,⟨sg33516,⟨sg33515,True.intro,True.intro⟩,True.intro⟩,⟨sg33518,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_135All : degreeTree62_135.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33530,⟨sg33525,⟨sg33522,⟨sg33521,⟨sg33520,True.intro,True.intro⟩,True.intro⟩,⟨sg33524,⟨sg33523,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33528,⟨sg33527,⟨sg33526,True.intro,True.intro⟩,True.intro⟩,⟨sg33529,True.intro,True.intro⟩⟩⟩,⟨sg33536,⟨sg33533,⟨sg33532,⟨sg33531,True.intro,True.intro⟩,True.intro⟩,⟨sg33535,⟨sg33534,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33539,⟨sg33538,⟨sg33537,True.intro,True.intro⟩,True.intro⟩,⟨sg33540,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_136All : degreeTree62_136.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33519,degreeTree62_134All,degreeTree62_135All⟩

lemma degreeTree62_137All : degreeTree62_137.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33552,⟨sg33547,⟨sg33544,⟨sg33543,⟨sg33542,True.intro,True.intro⟩,True.intro⟩,⟨sg33546,⟨sg33545,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33550,⟨sg33549,⟨sg33548,True.intro,True.intro⟩,True.intro⟩,⟨sg33551,True.intro,True.intro⟩⟩⟩,⟨sg33558,⟨sg33555,⟨sg33554,⟨sg33553,True.intro,True.intro⟩,True.intro⟩,⟨sg33557,⟨sg33556,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33561,⟨sg33560,⟨sg33559,True.intro,True.intro⟩,True.intro⟩,⟨sg33562,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_138All : degreeTree62_138.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33574,⟨sg33569,⟨sg33566,⟨sg33565,⟨sg33564,True.intro,True.intro⟩,True.intro⟩,⟨sg33568,⟨sg33567,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33572,⟨sg33571,⟨sg33570,True.intro,True.intro⟩,True.intro⟩,⟨sg33573,True.intro,True.intro⟩⟩⟩,⟨sg33580,⟨sg33577,⟨sg33576,⟨sg33575,True.intro,True.intro⟩,True.intro⟩,⟨sg33579,⟨sg33578,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33583,⟨sg33582,⟨sg33581,True.intro,True.intro⟩,True.intro⟩,⟨sg33584,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_139All : degreeTree62_139.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33563,degreeTree62_137All,degreeTree62_138All⟩

lemma degreeTree62_140All : degreeTree62_140.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33541,degreeTree62_136All,degreeTree62_139All⟩

lemma degreeTree62_141All : degreeTree62_141.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33497,degreeTree62_133All,degreeTree62_140All⟩

lemma degreeTree62_142All : degreeTree62_142.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33596,⟨sg33591,⟨sg33588,⟨sg33587,⟨sg33586,True.intro,True.intro⟩,True.intro⟩,⟨sg33590,⟨sg33589,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33594,⟨sg33593,⟨sg33592,True.intro,True.intro⟩,True.intro⟩,⟨sg33595,True.intro,True.intro⟩⟩⟩,⟨sg33602,⟨sg33599,⟨sg33598,⟨sg33597,True.intro,True.intro⟩,True.intro⟩,⟨sg33601,⟨sg33600,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33605,⟨sg33604,⟨sg33603,True.intro,True.intro⟩,True.intro⟩,⟨sg33606,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_143All : degreeTree62_143.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33618,⟨sg33613,⟨sg33610,⟨sg33609,⟨sg33608,True.intro,True.intro⟩,True.intro⟩,⟨sg33612,⟨sg33611,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33616,⟨sg33615,⟨sg33614,True.intro,True.intro⟩,True.intro⟩,⟨sg33617,True.intro,True.intro⟩⟩⟩,⟨sg33624,⟨sg33621,⟨sg33620,⟨sg33619,True.intro,True.intro⟩,True.intro⟩,⟨sg33623,⟨sg33622,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33627,⟨sg33626,⟨sg33625,True.intro,True.intro⟩,True.intro⟩,⟨sg33628,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_144All : degreeTree62_144.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33607,degreeTree62_142All,degreeTree62_143All⟩

lemma degreeTree62_145All : degreeTree62_145.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33640,⟨sg33635,⟨sg33632,⟨sg33631,⟨sg33630,True.intro,True.intro⟩,True.intro⟩,⟨sg33634,⟨sg33633,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33638,⟨sg33637,⟨sg33636,True.intro,True.intro⟩,True.intro⟩,⟨sg33639,True.intro,True.intro⟩⟩⟩,⟨sg33646,⟨sg33643,⟨sg33642,⟨sg33641,True.intro,True.intro⟩,True.intro⟩,⟨sg33645,⟨sg33644,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33649,⟨sg33648,⟨sg33647,True.intro,True.intro⟩,True.intro⟩,⟨sg33650,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_146All : degreeTree62_146.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33662,⟨sg33657,⟨sg33654,⟨sg33653,⟨sg33652,True.intro,True.intro⟩,True.intro⟩,⟨sg33656,⟨sg33655,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33660,⟨sg33659,⟨sg33658,True.intro,True.intro⟩,True.intro⟩,⟨sg33661,True.intro,True.intro⟩⟩⟩,⟨sg33668,⟨sg33665,⟨sg33664,⟨sg33663,True.intro,True.intro⟩,True.intro⟩,⟨sg33667,⟨sg33666,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33671,⟨sg33670,⟨sg33669,True.intro,True.intro⟩,True.intro⟩,⟨sg33672,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_147All : degreeTree62_147.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33651,degreeTree62_145All,degreeTree62_146All⟩

lemma degreeTree62_148All : degreeTree62_148.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33629,degreeTree62_144All,degreeTree62_147All⟩

lemma degreeTree62_149All : degreeTree62_149.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33684,⟨sg33679,⟨sg33676,⟨sg33675,⟨sg33674,True.intro,True.intro⟩,True.intro⟩,⟨sg33678,⟨sg33677,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33682,⟨sg33681,⟨sg33680,True.intro,True.intro⟩,True.intro⟩,⟨sg33683,True.intro,True.intro⟩⟩⟩,⟨sg33690,⟨sg33687,⟨sg33686,⟨sg33685,True.intro,True.intro⟩,True.intro⟩,⟨sg33689,⟨sg33688,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33693,⟨sg33692,⟨sg33691,True.intro,True.intro⟩,True.intro⟩,⟨sg33694,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_150All : degreeTree62_150.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33706,⟨sg33701,⟨sg33698,⟨sg33697,⟨sg33696,True.intro,True.intro⟩,True.intro⟩,⟨sg33700,⟨sg33699,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33704,⟨sg33703,⟨sg33702,True.intro,True.intro⟩,True.intro⟩,⟨sg33705,True.intro,True.intro⟩⟩⟩,⟨sg33712,⟨sg33709,⟨sg33708,⟨sg33707,True.intro,True.intro⟩,True.intro⟩,⟨sg33711,⟨sg33710,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33715,⟨sg33714,⟨sg33713,True.intro,True.intro⟩,True.intro⟩,⟨sg33716,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_151All : degreeTree62_151.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33695,degreeTree62_149All,degreeTree62_150All⟩

lemma degreeTree62_152All : degreeTree62_152.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33728,⟨sg33723,⟨sg33720,⟨sg33719,⟨sg33718,True.intro,True.intro⟩,True.intro⟩,⟨sg33722,⟨sg33721,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33726,⟨sg33725,⟨sg33724,True.intro,True.intro⟩,True.intro⟩,⟨sg33727,True.intro,True.intro⟩⟩⟩,⟨sg33734,⟨sg33731,⟨sg33730,⟨sg33729,True.intro,True.intro⟩,True.intro⟩,⟨sg33733,⟨sg33732,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33737,⟨sg33736,⟨sg33735,True.intro,True.intro⟩,True.intro⟩,⟨sg33738,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_153All : degreeTree62_153.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33750,⟨sg33745,⟨sg33742,⟨sg33741,⟨sg33740,True.intro,True.intro⟩,True.intro⟩,⟨sg33744,⟨sg33743,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33748,⟨sg33747,⟨sg33746,True.intro,True.intro⟩,True.intro⟩,⟨sg33749,True.intro,True.intro⟩⟩⟩,⟨sg33755,⟨sg33753,⟨sg33752,⟨sg33751,True.intro,True.intro⟩,True.intro⟩,⟨sg33754,True.intro,True.intro⟩⟩,⟨sg33758,⟨sg33757,⟨sg33756,True.intro,True.intro⟩,True.intro⟩,⟨sg33759,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_154All : degreeTree62_154.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33739,degreeTree62_152All,degreeTree62_153All⟩

lemma degreeTree62_155All : degreeTree62_155.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33717,degreeTree62_151All,degreeTree62_154All⟩

lemma degreeTree62_156All : degreeTree62_156.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33673,degreeTree62_148All,degreeTree62_155All⟩

lemma degreeTree62_157All : degreeTree62_157.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33585,degreeTree62_141All,degreeTree62_156All⟩

lemma degreeTree62_158All : degreeTree62_158.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33771,⟨sg33766,⟨sg33763,⟨sg33762,⟨sg33761,True.intro,True.intro⟩,True.intro⟩,⟨sg33765,⟨sg33764,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33769,⟨sg33768,⟨sg33767,True.intro,True.intro⟩,True.intro⟩,⟨sg33770,True.intro,True.intro⟩⟩⟩,⟨sg33777,⟨sg33774,⟨sg33773,⟨sg33772,True.intro,True.intro⟩,True.intro⟩,⟨sg33776,⟨sg33775,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33780,⟨sg33779,⟨sg33778,True.intro,True.intro⟩,True.intro⟩,⟨sg33781,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_159All : degreeTree62_159.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33793,⟨sg33788,⟨sg33785,⟨sg33784,⟨sg33783,True.intro,True.intro⟩,True.intro⟩,⟨sg33787,⟨sg33786,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33791,⟨sg33790,⟨sg33789,True.intro,True.intro⟩,True.intro⟩,⟨sg33792,True.intro,True.intro⟩⟩⟩,⟨sg33799,⟨sg33796,⟨sg33795,⟨sg33794,True.intro,True.intro⟩,True.intro⟩,⟨sg33798,⟨sg33797,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33802,⟨sg33801,⟨sg33800,True.intro,True.intro⟩,True.intro⟩,⟨sg33803,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_160All : degreeTree62_160.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33782,degreeTree62_158All,degreeTree62_159All⟩

lemma degreeTree62_161All : degreeTree62_161.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33815,⟨sg33810,⟨sg33807,⟨sg33806,⟨sg33805,True.intro,True.intro⟩,True.intro⟩,⟨sg33809,⟨sg33808,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33813,⟨sg33812,⟨sg33811,True.intro,True.intro⟩,True.intro⟩,⟨sg33814,True.intro,True.intro⟩⟩⟩,⟨sg33821,⟨sg33818,⟨sg33817,⟨sg33816,True.intro,True.intro⟩,True.intro⟩,⟨sg33820,⟨sg33819,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33824,⟨sg33823,⟨sg33822,True.intro,True.intro⟩,True.intro⟩,⟨sg33825,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_162All : degreeTree62_162.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33837,⟨sg33832,⟨sg33829,⟨sg33828,⟨sg33827,True.intro,True.intro⟩,True.intro⟩,⟨sg33831,⟨sg33830,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33835,⟨sg33834,⟨sg33833,True.intro,True.intro⟩,True.intro⟩,⟨sg33836,True.intro,True.intro⟩⟩⟩,⟨sg33843,⟨sg33840,⟨sg33839,⟨sg33838,True.intro,True.intro⟩,True.intro⟩,⟨sg33842,⟨sg33841,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33846,⟨sg33845,⟨sg33844,True.intro,True.intro⟩,True.intro⟩,⟨sg33847,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_163All : degreeTree62_163.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33826,degreeTree62_161All,degreeTree62_162All⟩

lemma degreeTree62_164All : degreeTree62_164.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33804,degreeTree62_160All,degreeTree62_163All⟩

lemma degreeTree62_165All : degreeTree62_165.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33859,⟨sg33854,⟨sg33851,⟨sg33850,⟨sg33849,True.intro,True.intro⟩,True.intro⟩,⟨sg33853,⟨sg33852,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33857,⟨sg33856,⟨sg33855,True.intro,True.intro⟩,True.intro⟩,⟨sg33858,True.intro,True.intro⟩⟩⟩,⟨sg33865,⟨sg33862,⟨sg33861,⟨sg33860,True.intro,True.intro⟩,True.intro⟩,⟨sg33864,⟨sg33863,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33868,⟨sg33867,⟨sg33866,True.intro,True.intro⟩,True.intro⟩,⟨sg33869,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_166All : degreeTree62_166.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33881,⟨sg33876,⟨sg33873,⟨sg33872,⟨sg33871,True.intro,True.intro⟩,True.intro⟩,⟨sg33875,⟨sg33874,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33879,⟨sg33878,⟨sg33877,True.intro,True.intro⟩,True.intro⟩,⟨sg33880,True.intro,True.intro⟩⟩⟩,⟨sg33887,⟨sg33884,⟨sg33883,⟨sg33882,True.intro,True.intro⟩,True.intro⟩,⟨sg33886,⟨sg33885,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33890,⟨sg33889,⟨sg33888,True.intro,True.intro⟩,True.intro⟩,⟨sg33891,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_167All : degreeTree62_167.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33870,degreeTree62_165All,degreeTree62_166All⟩

lemma degreeTree62_168All : degreeTree62_168.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33903,⟨sg33898,⟨sg33895,⟨sg33894,⟨sg33893,True.intro,True.intro⟩,True.intro⟩,⟨sg33897,⟨sg33896,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33901,⟨sg33900,⟨sg33899,True.intro,True.intro⟩,True.intro⟩,⟨sg33902,True.intro,True.intro⟩⟩⟩,⟨sg33909,⟨sg33906,⟨sg33905,⟨sg33904,True.intro,True.intro⟩,True.intro⟩,⟨sg33908,⟨sg33907,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33912,⟨sg33911,⟨sg33910,True.intro,True.intro⟩,True.intro⟩,⟨sg33913,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_169All : degreeTree62_169.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33925,⟨sg33920,⟨sg33917,⟨sg33916,⟨sg33915,True.intro,True.intro⟩,True.intro⟩,⟨sg33919,⟨sg33918,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33923,⟨sg33922,⟨sg33921,True.intro,True.intro⟩,True.intro⟩,⟨sg33924,True.intro,True.intro⟩⟩⟩,⟨sg33931,⟨sg33928,⟨sg33927,⟨sg33926,True.intro,True.intro⟩,True.intro⟩,⟨sg33930,⟨sg33929,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33934,⟨sg33933,⟨sg33932,True.intro,True.intro⟩,True.intro⟩,⟨sg33935,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_170All : degreeTree62_170.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33914,degreeTree62_168All,degreeTree62_169All⟩

lemma degreeTree62_171All : degreeTree62_171.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33892,degreeTree62_167All,degreeTree62_170All⟩

lemma degreeTree62_172All : degreeTree62_172.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33848,degreeTree62_164All,degreeTree62_171All⟩

lemma degreeTree62_173All : degreeTree62_173.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33947,⟨sg33942,⟨sg33939,⟨sg33938,⟨sg33937,True.intro,True.intro⟩,True.intro⟩,⟨sg33941,⟨sg33940,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33945,⟨sg33944,⟨sg33943,True.intro,True.intro⟩,True.intro⟩,⟨sg33946,True.intro,True.intro⟩⟩⟩,⟨sg33953,⟨sg33950,⟨sg33949,⟨sg33948,True.intro,True.intro⟩,True.intro⟩,⟨sg33952,⟨sg33951,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33956,⟨sg33955,⟨sg33954,True.intro,True.intro⟩,True.intro⟩,⟨sg33957,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_174All : degreeTree62_174.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33969,⟨sg33964,⟨sg33961,⟨sg33960,⟨sg33959,True.intro,True.intro⟩,True.intro⟩,⟨sg33963,⟨sg33962,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33967,⟨sg33966,⟨sg33965,True.intro,True.intro⟩,True.intro⟩,⟨sg33968,True.intro,True.intro⟩⟩⟩,⟨sg33975,⟨sg33972,⟨sg33971,⟨sg33970,True.intro,True.intro⟩,True.intro⟩,⟨sg33974,⟨sg33973,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33978,⟨sg33977,⟨sg33976,True.intro,True.intro⟩,True.intro⟩,⟨sg33979,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_175All : degreeTree62_175.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33958,degreeTree62_173All,degreeTree62_174All⟩

lemma degreeTree62_176All : degreeTree62_176.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33991,⟨sg33986,⟨sg33983,⟨sg33982,⟨sg33981,True.intro,True.intro⟩,True.intro⟩,⟨sg33985,⟨sg33984,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg33989,⟨sg33988,⟨sg33987,True.intro,True.intro⟩,True.intro⟩,⟨sg33990,True.intro,True.intro⟩⟩⟩,⟨sg33997,⟨sg33994,⟨sg33993,⟨sg33992,True.intro,True.intro⟩,True.intro⟩,⟨sg33996,⟨sg33995,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34000,⟨sg33999,⟨sg33998,True.intro,True.intro⟩,True.intro⟩,⟨sg34001,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_177All : degreeTree62_177.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34013,⟨sg34008,⟨sg34005,⟨sg34004,⟨sg34003,True.intro,True.intro⟩,True.intro⟩,⟨sg34007,⟨sg34006,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34011,⟨sg34010,⟨sg34009,True.intro,True.intro⟩,True.intro⟩,⟨sg34012,True.intro,True.intro⟩⟩⟩,⟨sg34019,⟨sg34016,⟨sg34015,⟨sg34014,True.intro,True.intro⟩,True.intro⟩,⟨sg34018,⟨sg34017,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34022,⟨sg34021,⟨sg34020,True.intro,True.intro⟩,True.intro⟩,⟨sg34023,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_178All : degreeTree62_178.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34002,degreeTree62_176All,degreeTree62_177All⟩

lemma degreeTree62_179All : degreeTree62_179.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33980,degreeTree62_175All,degreeTree62_178All⟩

lemma degreeTree62_180All : degreeTree62_180.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34035,⟨sg34030,⟨sg34027,⟨sg34026,⟨sg34025,True.intro,True.intro⟩,True.intro⟩,⟨sg34029,⟨sg34028,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34033,⟨sg34032,⟨sg34031,True.intro,True.intro⟩,True.intro⟩,⟨sg34034,True.intro,True.intro⟩⟩⟩,⟨sg34041,⟨sg34038,⟨sg34037,⟨sg34036,True.intro,True.intro⟩,True.intro⟩,⟨sg34040,⟨sg34039,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34044,⟨sg34043,⟨sg34042,True.intro,True.intro⟩,True.intro⟩,⟨sg34045,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_181All : degreeTree62_181.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34057,⟨sg34052,⟨sg34049,⟨sg34048,⟨sg34047,True.intro,True.intro⟩,True.intro⟩,⟨sg34051,⟨sg34050,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34055,⟨sg34054,⟨sg34053,True.intro,True.intro⟩,True.intro⟩,⟨sg34056,True.intro,True.intro⟩⟩⟩,⟨sg34063,⟨sg34060,⟨sg34059,⟨sg34058,True.intro,True.intro⟩,True.intro⟩,⟨sg34062,⟨sg34061,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34066,⟨sg34065,⟨sg34064,True.intro,True.intro⟩,True.intro⟩,⟨sg34067,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_182All : degreeTree62_182.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34046,degreeTree62_180All,degreeTree62_181All⟩

lemma degreeTree62_183All : degreeTree62_183.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34079,⟨sg34074,⟨sg34071,⟨sg34070,⟨sg34069,True.intro,True.intro⟩,True.intro⟩,⟨sg34073,⟨sg34072,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34077,⟨sg34076,⟨sg34075,True.intro,True.intro⟩,True.intro⟩,⟨sg34078,True.intro,True.intro⟩⟩⟩,⟨sg34085,⟨sg34082,⟨sg34081,⟨sg34080,True.intro,True.intro⟩,True.intro⟩,⟨sg34084,⟨sg34083,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34088,⟨sg34087,⟨sg34086,True.intro,True.intro⟩,True.intro⟩,⟨sg34089,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_184All : degreeTree62_184.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34101,⟨sg34096,⟨sg34093,⟨sg34092,⟨sg34091,True.intro,True.intro⟩,True.intro⟩,⟨sg34095,⟨sg34094,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34099,⟨sg34098,⟨sg34097,True.intro,True.intro⟩,True.intro⟩,⟨sg34100,True.intro,True.intro⟩⟩⟩,⟨sg34106,⟨sg34104,⟨sg34103,⟨sg34102,True.intro,True.intro⟩,True.intro⟩,⟨sg34105,True.intro,True.intro⟩⟩,⟨sg34109,⟨sg34108,⟨sg34107,True.intro,True.intro⟩,True.intro⟩,⟨sg34110,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_185All : degreeTree62_185.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34090,degreeTree62_183All,degreeTree62_184All⟩

lemma degreeTree62_186All : degreeTree62_186.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34068,degreeTree62_182All,degreeTree62_185All⟩

lemma degreeTree62_187All : degreeTree62_187.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34024,degreeTree62_179All,degreeTree62_186All⟩

lemma degreeTree62_188All : degreeTree62_188.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33936,degreeTree62_172All,degreeTree62_187All⟩

lemma degreeTree62_189All : degreeTree62_189.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33760,degreeTree62_157All,degreeTree62_188All⟩

lemma degreeTree62_190All : degreeTree62_190.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34122,⟨sg34117,⟨sg34114,⟨sg34113,⟨sg34112,True.intro,True.intro⟩,True.intro⟩,⟨sg34116,⟨sg34115,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34120,⟨sg34119,⟨sg34118,True.intro,True.intro⟩,True.intro⟩,⟨sg34121,True.intro,True.intro⟩⟩⟩,⟨sg34128,⟨sg34125,⟨sg34124,⟨sg34123,True.intro,True.intro⟩,True.intro⟩,⟨sg34127,⟨sg34126,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34131,⟨sg34130,⟨sg34129,True.intro,True.intro⟩,True.intro⟩,⟨sg34132,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_191All : degreeTree62_191.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34144,⟨sg34139,⟨sg34136,⟨sg34135,⟨sg34134,True.intro,True.intro⟩,True.intro⟩,⟨sg34138,⟨sg34137,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34142,⟨sg34141,⟨sg34140,True.intro,True.intro⟩,True.intro⟩,⟨sg34143,True.intro,True.intro⟩⟩⟩,⟨sg34150,⟨sg34147,⟨sg34146,⟨sg34145,True.intro,True.intro⟩,True.intro⟩,⟨sg34149,⟨sg34148,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34153,⟨sg34152,⟨sg34151,True.intro,True.intro⟩,True.intro⟩,⟨sg34154,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_192All : degreeTree62_192.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34133,degreeTree62_190All,degreeTree62_191All⟩

lemma degreeTree62_193All : degreeTree62_193.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34166,⟨sg34161,⟨sg34158,⟨sg34157,⟨sg34156,True.intro,True.intro⟩,True.intro⟩,⟨sg34160,⟨sg34159,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34164,⟨sg34163,⟨sg34162,True.intro,True.intro⟩,True.intro⟩,⟨sg34165,True.intro,True.intro⟩⟩⟩,⟨sg34172,⟨sg34169,⟨sg34168,⟨sg34167,True.intro,True.intro⟩,True.intro⟩,⟨sg34171,⟨sg34170,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34175,⟨sg34174,⟨sg34173,True.intro,True.intro⟩,True.intro⟩,⟨sg34176,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_194All : degreeTree62_194.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34188,⟨sg34183,⟨sg34180,⟨sg34179,⟨sg34178,True.intro,True.intro⟩,True.intro⟩,⟨sg34182,⟨sg34181,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34186,⟨sg34185,⟨sg34184,True.intro,True.intro⟩,True.intro⟩,⟨sg34187,True.intro,True.intro⟩⟩⟩,⟨sg34194,⟨sg34191,⟨sg34190,⟨sg34189,True.intro,True.intro⟩,True.intro⟩,⟨sg34193,⟨sg34192,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34197,⟨sg34196,⟨sg34195,True.intro,True.intro⟩,True.intro⟩,⟨sg34198,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_195All : degreeTree62_195.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34177,degreeTree62_193All,degreeTree62_194All⟩

lemma degreeTree62_196All : degreeTree62_196.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34155,degreeTree62_192All,degreeTree62_195All⟩

lemma degreeTree62_197All : degreeTree62_197.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34210,⟨sg34205,⟨sg34202,⟨sg34201,⟨sg34200,True.intro,True.intro⟩,True.intro⟩,⟨sg34204,⟨sg34203,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34208,⟨sg34207,⟨sg34206,True.intro,True.intro⟩,True.intro⟩,⟨sg34209,True.intro,True.intro⟩⟩⟩,⟨sg34216,⟨sg34213,⟨sg34212,⟨sg34211,True.intro,True.intro⟩,True.intro⟩,⟨sg34215,⟨sg34214,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34219,⟨sg34218,⟨sg34217,True.intro,True.intro⟩,True.intro⟩,⟨sg34220,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_198All : degreeTree62_198.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34232,⟨sg34227,⟨sg34224,⟨sg34223,⟨sg34222,True.intro,True.intro⟩,True.intro⟩,⟨sg34226,⟨sg34225,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34230,⟨sg34229,⟨sg34228,True.intro,True.intro⟩,True.intro⟩,⟨sg34231,True.intro,True.intro⟩⟩⟩,⟨sg34238,⟨sg34235,⟨sg34234,⟨sg34233,True.intro,True.intro⟩,True.intro⟩,⟨sg34237,⟨sg34236,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34241,⟨sg34240,⟨sg34239,True.intro,True.intro⟩,True.intro⟩,⟨sg34242,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_199All : degreeTree62_199.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34221,degreeTree62_197All,degreeTree62_198All⟩

lemma degreeTree62_200All : degreeTree62_200.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34254,⟨sg34249,⟨sg34246,⟨sg34245,⟨sg34244,True.intro,True.intro⟩,True.intro⟩,⟨sg34248,⟨sg34247,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34252,⟨sg34251,⟨sg34250,True.intro,True.intro⟩,True.intro⟩,⟨sg34253,True.intro,True.intro⟩⟩⟩,⟨sg34260,⟨sg34257,⟨sg34256,⟨sg34255,True.intro,True.intro⟩,True.intro⟩,⟨sg34259,⟨sg34258,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34263,⟨sg34262,⟨sg34261,True.intro,True.intro⟩,True.intro⟩,⟨sg34264,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_201All : degreeTree62_201.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34276,⟨sg34271,⟨sg34268,⟨sg34267,⟨sg34266,True.intro,True.intro⟩,True.intro⟩,⟨sg34270,⟨sg34269,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34274,⟨sg34273,⟨sg34272,True.intro,True.intro⟩,True.intro⟩,⟨sg34275,True.intro,True.intro⟩⟩⟩,⟨sg34282,⟨sg34279,⟨sg34278,⟨sg34277,True.intro,True.intro⟩,True.intro⟩,⟨sg34281,⟨sg34280,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34285,⟨sg34284,⟨sg34283,True.intro,True.intro⟩,True.intro⟩,⟨sg34286,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_202All : degreeTree62_202.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34265,degreeTree62_200All,degreeTree62_201All⟩

lemma degreeTree62_203All : degreeTree62_203.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34243,degreeTree62_199All,degreeTree62_202All⟩

lemma degreeTree62_204All : degreeTree62_204.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34199,degreeTree62_196All,degreeTree62_203All⟩

lemma degreeTree62_205All : degreeTree62_205.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34298,⟨sg34293,⟨sg34290,⟨sg34289,⟨sg34288,True.intro,True.intro⟩,True.intro⟩,⟨sg34292,⟨sg34291,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34296,⟨sg34295,⟨sg34294,True.intro,True.intro⟩,True.intro⟩,⟨sg34297,True.intro,True.intro⟩⟩⟩,⟨sg34304,⟨sg34301,⟨sg34300,⟨sg34299,True.intro,True.intro⟩,True.intro⟩,⟨sg34303,⟨sg34302,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34307,⟨sg34306,⟨sg34305,True.intro,True.intro⟩,True.intro⟩,⟨sg34308,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_206All : degreeTree62_206.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34320,⟨sg34315,⟨sg34312,⟨sg34311,⟨sg34310,True.intro,True.intro⟩,True.intro⟩,⟨sg34314,⟨sg34313,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34318,⟨sg34317,⟨sg34316,True.intro,True.intro⟩,True.intro⟩,⟨sg34319,True.intro,True.intro⟩⟩⟩,⟨sg34326,⟨sg34323,⟨sg34322,⟨sg34321,True.intro,True.intro⟩,True.intro⟩,⟨sg34325,⟨sg34324,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34329,⟨sg34328,⟨sg34327,True.intro,True.intro⟩,True.intro⟩,⟨sg34330,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_207All : degreeTree62_207.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34309,degreeTree62_205All,degreeTree62_206All⟩

lemma degreeTree62_208All : degreeTree62_208.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34342,⟨sg34337,⟨sg34334,⟨sg34333,⟨sg34332,True.intro,True.intro⟩,True.intro⟩,⟨sg34336,⟨sg34335,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34340,⟨sg34339,⟨sg34338,True.intro,True.intro⟩,True.intro⟩,⟨sg34341,True.intro,True.intro⟩⟩⟩,⟨sg34348,⟨sg34345,⟨sg34344,⟨sg34343,True.intro,True.intro⟩,True.intro⟩,⟨sg34347,⟨sg34346,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34351,⟨sg34350,⟨sg34349,True.intro,True.intro⟩,True.intro⟩,⟨sg34352,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_209All : degreeTree62_209.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34364,⟨sg34359,⟨sg34356,⟨sg34355,⟨sg34354,True.intro,True.intro⟩,True.intro⟩,⟨sg34358,⟨sg34357,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34362,⟨sg34361,⟨sg34360,True.intro,True.intro⟩,True.intro⟩,⟨sg34363,True.intro,True.intro⟩⟩⟩,⟨sg34370,⟨sg34367,⟨sg34366,⟨sg34365,True.intro,True.intro⟩,True.intro⟩,⟨sg34369,⟨sg34368,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34373,⟨sg34372,⟨sg34371,True.intro,True.intro⟩,True.intro⟩,⟨sg34374,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_210All : degreeTree62_210.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34353,degreeTree62_208All,degreeTree62_209All⟩

lemma degreeTree62_211All : degreeTree62_211.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34331,degreeTree62_207All,degreeTree62_210All⟩

lemma degreeTree62_212All : degreeTree62_212.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34386,⟨sg34381,⟨sg34378,⟨sg34377,⟨sg34376,True.intro,True.intro⟩,True.intro⟩,⟨sg34380,⟨sg34379,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34384,⟨sg34383,⟨sg34382,True.intro,True.intro⟩,True.intro⟩,⟨sg34385,True.intro,True.intro⟩⟩⟩,⟨sg34392,⟨sg34389,⟨sg34388,⟨sg34387,True.intro,True.intro⟩,True.intro⟩,⟨sg34391,⟨sg34390,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34395,⟨sg34394,⟨sg34393,True.intro,True.intro⟩,True.intro⟩,⟨sg34396,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_213All : degreeTree62_213.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34408,⟨sg34403,⟨sg34400,⟨sg34399,⟨sg34398,True.intro,True.intro⟩,True.intro⟩,⟨sg34402,⟨sg34401,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34406,⟨sg34405,⟨sg34404,True.intro,True.intro⟩,True.intro⟩,⟨sg34407,True.intro,True.intro⟩⟩⟩,⟨sg34414,⟨sg34411,⟨sg34410,⟨sg34409,True.intro,True.intro⟩,True.intro⟩,⟨sg34413,⟨sg34412,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34417,⟨sg34416,⟨sg34415,True.intro,True.intro⟩,True.intro⟩,⟨sg34418,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_214All : degreeTree62_214.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34397,degreeTree62_212All,degreeTree62_213All⟩

lemma degreeTree62_215All : degreeTree62_215.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34430,⟨sg34425,⟨sg34422,⟨sg34421,⟨sg34420,True.intro,True.intro⟩,True.intro⟩,⟨sg34424,⟨sg34423,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34428,⟨sg34427,⟨sg34426,True.intro,True.intro⟩,True.intro⟩,⟨sg34429,True.intro,True.intro⟩⟩⟩,⟨sg34436,⟨sg34433,⟨sg34432,⟨sg34431,True.intro,True.intro⟩,True.intro⟩,⟨sg34435,⟨sg34434,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34439,⟨sg34438,⟨sg34437,True.intro,True.intro⟩,True.intro⟩,⟨sg34440,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_216All : degreeTree62_216.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34452,⟨sg34447,⟨sg34444,⟨sg34443,⟨sg34442,True.intro,True.intro⟩,True.intro⟩,⟨sg34446,⟨sg34445,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34450,⟨sg34449,⟨sg34448,True.intro,True.intro⟩,True.intro⟩,⟨sg34451,True.intro,True.intro⟩⟩⟩,⟨sg34457,⟨sg34455,⟨sg34454,⟨sg34453,True.intro,True.intro⟩,True.intro⟩,⟨sg34456,True.intro,True.intro⟩⟩,⟨sg34460,⟨sg34459,⟨sg34458,True.intro,True.intro⟩,True.intro⟩,⟨sg34461,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_217All : degreeTree62_217.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34441,degreeTree62_215All,degreeTree62_216All⟩

lemma degreeTree62_218All : degreeTree62_218.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34419,degreeTree62_214All,degreeTree62_217All⟩

lemma degreeTree62_219All : degreeTree62_219.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34375,degreeTree62_211All,degreeTree62_218All⟩

lemma degreeTree62_220All : degreeTree62_220.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34287,degreeTree62_204All,degreeTree62_219All⟩

lemma degreeTree62_221All : degreeTree62_221.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34473,⟨sg34468,⟨sg34465,⟨sg34464,⟨sg34463,True.intro,True.intro⟩,True.intro⟩,⟨sg34467,⟨sg34466,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34471,⟨sg34470,⟨sg34469,True.intro,True.intro⟩,True.intro⟩,⟨sg34472,True.intro,True.intro⟩⟩⟩,⟨sg34479,⟨sg34476,⟨sg34475,⟨sg34474,True.intro,True.intro⟩,True.intro⟩,⟨sg34478,⟨sg34477,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34482,⟨sg34481,⟨sg34480,True.intro,True.intro⟩,True.intro⟩,⟨sg34483,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_222All : degreeTree62_222.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34495,⟨sg34490,⟨sg34487,⟨sg34486,⟨sg34485,True.intro,True.intro⟩,True.intro⟩,⟨sg34489,⟨sg34488,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34493,⟨sg34492,⟨sg34491,True.intro,True.intro⟩,True.intro⟩,⟨sg34494,True.intro,True.intro⟩⟩⟩,⟨sg34501,⟨sg34498,⟨sg34497,⟨sg34496,True.intro,True.intro⟩,True.intro⟩,⟨sg34500,⟨sg34499,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34504,⟨sg34503,⟨sg34502,True.intro,True.intro⟩,True.intro⟩,⟨sg34505,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_223All : degreeTree62_223.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34484,degreeTree62_221All,degreeTree62_222All⟩

lemma degreeTree62_224All : degreeTree62_224.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34517,⟨sg34512,⟨sg34509,⟨sg34508,⟨sg34507,True.intro,True.intro⟩,True.intro⟩,⟨sg34511,⟨sg34510,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34515,⟨sg34514,⟨sg34513,True.intro,True.intro⟩,True.intro⟩,⟨sg34516,True.intro,True.intro⟩⟩⟩,⟨sg34523,⟨sg34520,⟨sg34519,⟨sg34518,True.intro,True.intro⟩,True.intro⟩,⟨sg34522,⟨sg34521,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34526,⟨sg34525,⟨sg34524,True.intro,True.intro⟩,True.intro⟩,⟨sg34527,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_225All : degreeTree62_225.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34539,⟨sg34534,⟨sg34531,⟨sg34530,⟨sg34529,True.intro,True.intro⟩,True.intro⟩,⟨sg34533,⟨sg34532,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34537,⟨sg34536,⟨sg34535,True.intro,True.intro⟩,True.intro⟩,⟨sg34538,True.intro,True.intro⟩⟩⟩,⟨sg34545,⟨sg34542,⟨sg34541,⟨sg34540,True.intro,True.intro⟩,True.intro⟩,⟨sg34544,⟨sg34543,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34548,⟨sg34547,⟨sg34546,True.intro,True.intro⟩,True.intro⟩,⟨sg34549,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_226All : degreeTree62_226.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34528,degreeTree62_224All,degreeTree62_225All⟩

lemma degreeTree62_227All : degreeTree62_227.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34506,degreeTree62_223All,degreeTree62_226All⟩

lemma degreeTree62_228All : degreeTree62_228.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34561,⟨sg34556,⟨sg34553,⟨sg34552,⟨sg34551,True.intro,True.intro⟩,True.intro⟩,⟨sg34555,⟨sg34554,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34559,⟨sg34558,⟨sg34557,True.intro,True.intro⟩,True.intro⟩,⟨sg34560,True.intro,True.intro⟩⟩⟩,⟨sg34567,⟨sg34564,⟨sg34563,⟨sg34562,True.intro,True.intro⟩,True.intro⟩,⟨sg34566,⟨sg34565,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34570,⟨sg34569,⟨sg34568,True.intro,True.intro⟩,True.intro⟩,⟨sg34571,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_229All : degreeTree62_229.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34583,⟨sg34578,⟨sg34575,⟨sg34574,⟨sg34573,True.intro,True.intro⟩,True.intro⟩,⟨sg34577,⟨sg34576,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34581,⟨sg34580,⟨sg34579,True.intro,True.intro⟩,True.intro⟩,⟨sg34582,True.intro,True.intro⟩⟩⟩,⟨sg34589,⟨sg34586,⟨sg34585,⟨sg34584,True.intro,True.intro⟩,True.intro⟩,⟨sg34588,⟨sg34587,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34592,⟨sg34591,⟨sg34590,True.intro,True.intro⟩,True.intro⟩,⟨sg34593,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_230All : degreeTree62_230.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34572,degreeTree62_228All,degreeTree62_229All⟩

lemma degreeTree62_231All : degreeTree62_231.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34605,⟨sg34600,⟨sg34597,⟨sg34596,⟨sg34595,True.intro,True.intro⟩,True.intro⟩,⟨sg34599,⟨sg34598,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34603,⟨sg34602,⟨sg34601,True.intro,True.intro⟩,True.intro⟩,⟨sg34604,True.intro,True.intro⟩⟩⟩,⟨sg34611,⟨sg34608,⟨sg34607,⟨sg34606,True.intro,True.intro⟩,True.intro⟩,⟨sg34610,⟨sg34609,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34614,⟨sg34613,⟨sg34612,True.intro,True.intro⟩,True.intro⟩,⟨sg34615,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_232All : degreeTree62_232.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34627,⟨sg34622,⟨sg34619,⟨sg34618,⟨sg34617,True.intro,True.intro⟩,True.intro⟩,⟨sg34621,⟨sg34620,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34625,⟨sg34624,⟨sg34623,True.intro,True.intro⟩,True.intro⟩,⟨sg34626,True.intro,True.intro⟩⟩⟩,⟨sg34632,⟨sg34630,⟨sg34629,⟨sg34628,True.intro,True.intro⟩,True.intro⟩,⟨sg34631,True.intro,True.intro⟩⟩,⟨sg34635,⟨sg34634,⟨sg34633,True.intro,True.intro⟩,True.intro⟩,⟨sg34636,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_233All : degreeTree62_233.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34616,degreeTree62_231All,degreeTree62_232All⟩

lemma degreeTree62_234All : degreeTree62_234.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34594,degreeTree62_230All,degreeTree62_233All⟩

lemma degreeTree62_235All : degreeTree62_235.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34550,degreeTree62_227All,degreeTree62_234All⟩

lemma degreeTree62_236All : degreeTree62_236.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34648,⟨sg34643,⟨sg34640,⟨sg34639,⟨sg34638,True.intro,True.intro⟩,True.intro⟩,⟨sg34642,⟨sg34641,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34646,⟨sg34645,⟨sg34644,True.intro,True.intro⟩,True.intro⟩,⟨sg34647,True.intro,True.intro⟩⟩⟩,⟨sg34654,⟨sg34651,⟨sg34650,⟨sg34649,True.intro,True.intro⟩,True.intro⟩,⟨sg34653,⟨sg34652,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34657,⟨sg34656,⟨sg34655,True.intro,True.intro⟩,True.intro⟩,⟨sg34658,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_237All : degreeTree62_237.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34670,⟨sg34665,⟨sg34662,⟨sg34661,⟨sg34660,True.intro,True.intro⟩,True.intro⟩,⟨sg34664,⟨sg34663,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34668,⟨sg34667,⟨sg34666,True.intro,True.intro⟩,True.intro⟩,⟨sg34669,True.intro,True.intro⟩⟩⟩,⟨sg34676,⟨sg34673,⟨sg34672,⟨sg34671,True.intro,True.intro⟩,True.intro⟩,⟨sg34675,⟨sg34674,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34679,⟨sg34678,⟨sg34677,True.intro,True.intro⟩,True.intro⟩,⟨sg34680,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_238All : degreeTree62_238.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34659,degreeTree62_236All,degreeTree62_237All⟩

lemma degreeTree62_239All : degreeTree62_239.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34692,⟨sg34687,⟨sg34684,⟨sg34683,⟨sg34682,True.intro,True.intro⟩,True.intro⟩,⟨sg34686,⟨sg34685,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34690,⟨sg34689,⟨sg34688,True.intro,True.intro⟩,True.intro⟩,⟨sg34691,True.intro,True.intro⟩⟩⟩,⟨sg34698,⟨sg34695,⟨sg34694,⟨sg34693,True.intro,True.intro⟩,True.intro⟩,⟨sg34697,⟨sg34696,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34701,⟨sg34700,⟨sg34699,True.intro,True.intro⟩,True.intro⟩,⟨sg34702,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_240All : degreeTree62_240.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34714,⟨sg34709,⟨sg34706,⟨sg34705,⟨sg34704,True.intro,True.intro⟩,True.intro⟩,⟨sg34708,⟨sg34707,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34712,⟨sg34711,⟨sg34710,True.intro,True.intro⟩,True.intro⟩,⟨sg34713,True.intro,True.intro⟩⟩⟩,⟨sg34720,⟨sg34717,⟨sg34716,⟨sg34715,True.intro,True.intro⟩,True.intro⟩,⟨sg34719,⟨sg34718,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34723,⟨sg34722,⟨sg34721,True.intro,True.intro⟩,True.intro⟩,⟨sg34724,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_241All : degreeTree62_241.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34703,degreeTree62_239All,degreeTree62_240All⟩

lemma degreeTree62_242All : degreeTree62_242.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34681,degreeTree62_238All,degreeTree62_241All⟩

lemma degreeTree62_243All : degreeTree62_243.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34736,⟨sg34731,⟨sg34728,⟨sg34727,⟨sg34726,True.intro,True.intro⟩,True.intro⟩,⟨sg34730,⟨sg34729,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34734,⟨sg34733,⟨sg34732,True.intro,True.intro⟩,True.intro⟩,⟨sg34735,True.intro,True.intro⟩⟩⟩,⟨sg34742,⟨sg34739,⟨sg34738,⟨sg34737,True.intro,True.intro⟩,True.intro⟩,⟨sg34741,⟨sg34740,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34745,⟨sg34744,⟨sg34743,True.intro,True.intro⟩,True.intro⟩,⟨sg34746,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_244All : degreeTree62_244.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34758,⟨sg34753,⟨sg34750,⟨sg34749,⟨sg34748,True.intro,True.intro⟩,True.intro⟩,⟨sg34752,⟨sg34751,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34756,⟨sg34755,⟨sg34754,True.intro,True.intro⟩,True.intro⟩,⟨sg34757,True.intro,True.intro⟩⟩⟩,⟨sg34764,⟨sg34761,⟨sg34760,⟨sg34759,True.intro,True.intro⟩,True.intro⟩,⟨sg34763,⟨sg34762,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34767,⟨sg34766,⟨sg34765,True.intro,True.intro⟩,True.intro⟩,⟨sg34768,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_245All : degreeTree62_245.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34747,degreeTree62_243All,degreeTree62_244All⟩

lemma degreeTree62_246All : degreeTree62_246.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34780,⟨sg34775,⟨sg34772,⟨sg34771,⟨sg34770,True.intro,True.intro⟩,True.intro⟩,⟨sg34774,⟨sg34773,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34778,⟨sg34777,⟨sg34776,True.intro,True.intro⟩,True.intro⟩,⟨sg34779,True.intro,True.intro⟩⟩⟩,⟨sg34786,⟨sg34783,⟨sg34782,⟨sg34781,True.intro,True.intro⟩,True.intro⟩,⟨sg34785,⟨sg34784,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34789,⟨sg34788,⟨sg34787,True.intro,True.intro⟩,True.intro⟩,⟨sg34790,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_247All : degreeTree62_247.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34802,⟨sg34797,⟨sg34794,⟨sg34793,⟨sg34792,True.intro,True.intro⟩,True.intro⟩,⟨sg34796,⟨sg34795,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34800,⟨sg34799,⟨sg34798,True.intro,True.intro⟩,True.intro⟩,⟨sg34801,True.intro,True.intro⟩⟩⟩,⟨sg34807,⟨sg34805,⟨sg34804,⟨sg34803,True.intro,True.intro⟩,True.intro⟩,⟨sg34806,True.intro,True.intro⟩⟩,⟨sg34810,⟨sg34809,⟨sg34808,True.intro,True.intro⟩,True.intro⟩,⟨sg34811,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_248All : degreeTree62_248.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34791,degreeTree62_246All,degreeTree62_247All⟩

lemma degreeTree62_249All : degreeTree62_249.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34769,degreeTree62_245All,degreeTree62_248All⟩

lemma degreeTree62_250All : degreeTree62_250.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34725,degreeTree62_242All,degreeTree62_249All⟩

lemma degreeTree62_251All : degreeTree62_251.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34637,degreeTree62_235All,degreeTree62_250All⟩

lemma degreeTree62_252All : degreeTree62_252.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34462,degreeTree62_220All,degreeTree62_251All⟩

lemma degreeTree62_253All : degreeTree62_253.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34111,degreeTree62_189All,degreeTree62_252All⟩

lemma degreeTree62_254All : degreeTree62_254.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg33409,degreeTree62_126All,degreeTree62_253All⟩

lemma degreeTree62_255All : degreeTree62_255.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34823,⟨sg34818,⟨sg34815,⟨sg34814,⟨sg34813,True.intro,True.intro⟩,True.intro⟩,⟨sg34817,⟨sg34816,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34821,⟨sg34820,⟨sg34819,True.intro,True.intro⟩,True.intro⟩,⟨sg34822,True.intro,True.intro⟩⟩⟩,⟨sg34829,⟨sg34826,⟨sg34825,⟨sg34824,True.intro,True.intro⟩,True.intro⟩,⟨sg34828,⟨sg34827,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34832,⟨sg34831,⟨sg34830,True.intro,True.intro⟩,True.intro⟩,⟨sg34833,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_256All : degreeTree62_256.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34845,⟨sg34840,⟨sg34837,⟨sg34836,⟨sg34835,True.intro,True.intro⟩,True.intro⟩,⟨sg34839,⟨sg34838,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34843,⟨sg34842,⟨sg34841,True.intro,True.intro⟩,True.intro⟩,⟨sg34844,True.intro,True.intro⟩⟩⟩,⟨sg34851,⟨sg34848,⟨sg34847,⟨sg34846,True.intro,True.intro⟩,True.intro⟩,⟨sg34850,⟨sg34849,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34854,⟨sg34853,⟨sg34852,True.intro,True.intro⟩,True.intro⟩,⟨sg34855,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_257All : degreeTree62_257.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34834,degreeTree62_255All,degreeTree62_256All⟩

lemma degreeTree62_258All : degreeTree62_258.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34867,⟨sg34862,⟨sg34859,⟨sg34858,⟨sg34857,True.intro,True.intro⟩,True.intro⟩,⟨sg34861,⟨sg34860,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34865,⟨sg34864,⟨sg34863,True.intro,True.intro⟩,True.intro⟩,⟨sg34866,True.intro,True.intro⟩⟩⟩,⟨sg34873,⟨sg34870,⟨sg34869,⟨sg34868,True.intro,True.intro⟩,True.intro⟩,⟨sg34872,⟨sg34871,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34876,⟨sg34875,⟨sg34874,True.intro,True.intro⟩,True.intro⟩,⟨sg34877,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_259All : degreeTree62_259.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34889,⟨sg34884,⟨sg34881,⟨sg34880,⟨sg34879,True.intro,True.intro⟩,True.intro⟩,⟨sg34883,⟨sg34882,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34887,⟨sg34886,⟨sg34885,True.intro,True.intro⟩,True.intro⟩,⟨sg34888,True.intro,True.intro⟩⟩⟩,⟨sg34895,⟨sg34892,⟨sg34891,⟨sg34890,True.intro,True.intro⟩,True.intro⟩,⟨sg34894,⟨sg34893,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34898,⟨sg34897,⟨sg34896,True.intro,True.intro⟩,True.intro⟩,⟨sg34899,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_260All : degreeTree62_260.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34878,degreeTree62_258All,degreeTree62_259All⟩

lemma degreeTree62_261All : degreeTree62_261.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34856,degreeTree62_257All,degreeTree62_260All⟩

lemma degreeTree62_262All : degreeTree62_262.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34911,⟨sg34906,⟨sg34903,⟨sg34902,⟨sg34901,True.intro,True.intro⟩,True.intro⟩,⟨sg34905,⟨sg34904,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34909,⟨sg34908,⟨sg34907,True.intro,True.intro⟩,True.intro⟩,⟨sg34910,True.intro,True.intro⟩⟩⟩,⟨sg34917,⟨sg34914,⟨sg34913,⟨sg34912,True.intro,True.intro⟩,True.intro⟩,⟨sg34916,⟨sg34915,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34920,⟨sg34919,⟨sg34918,True.intro,True.intro⟩,True.intro⟩,⟨sg34921,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_263All : degreeTree62_263.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34933,⟨sg34928,⟨sg34925,⟨sg34924,⟨sg34923,True.intro,True.intro⟩,True.intro⟩,⟨sg34927,⟨sg34926,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34931,⟨sg34930,⟨sg34929,True.intro,True.intro⟩,True.intro⟩,⟨sg34932,True.intro,True.intro⟩⟩⟩,⟨sg34939,⟨sg34936,⟨sg34935,⟨sg34934,True.intro,True.intro⟩,True.intro⟩,⟨sg34938,⟨sg34937,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34942,⟨sg34941,⟨sg34940,True.intro,True.intro⟩,True.intro⟩,⟨sg34943,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_264All : degreeTree62_264.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34922,degreeTree62_262All,degreeTree62_263All⟩

lemma degreeTree62_265All : degreeTree62_265.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34955,⟨sg34950,⟨sg34947,⟨sg34946,⟨sg34945,True.intro,True.intro⟩,True.intro⟩,⟨sg34949,⟨sg34948,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34953,⟨sg34952,⟨sg34951,True.intro,True.intro⟩,True.intro⟩,⟨sg34954,True.intro,True.intro⟩⟩⟩,⟨sg34961,⟨sg34958,⟨sg34957,⟨sg34956,True.intro,True.intro⟩,True.intro⟩,⟨sg34960,⟨sg34959,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34964,⟨sg34963,⟨sg34962,True.intro,True.intro⟩,True.intro⟩,⟨sg34965,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_266All : degreeTree62_266.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34977,⟨sg34972,⟨sg34969,⟨sg34968,⟨sg34967,True.intro,True.intro⟩,True.intro⟩,⟨sg34971,⟨sg34970,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34975,⟨sg34974,⟨sg34973,True.intro,True.intro⟩,True.intro⟩,⟨sg34976,True.intro,True.intro⟩⟩⟩,⟨sg34983,⟨sg34980,⟨sg34979,⟨sg34978,True.intro,True.intro⟩,True.intro⟩,⟨sg34982,⟨sg34981,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34986,⟨sg34985,⟨sg34984,True.intro,True.intro⟩,True.intro⟩,⟨sg34987,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_267All : degreeTree62_267.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34966,degreeTree62_265All,degreeTree62_266All⟩

lemma degreeTree62_268All : degreeTree62_268.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34944,degreeTree62_264All,degreeTree62_267All⟩

lemma degreeTree62_269All : degreeTree62_269.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34900,degreeTree62_261All,degreeTree62_268All⟩

lemma degreeTree62_270All : degreeTree62_270.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34999,⟨sg34994,⟨sg34991,⟨sg34990,⟨sg34989,True.intro,True.intro⟩,True.intro⟩,⟨sg34993,⟨sg34992,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg34997,⟨sg34996,⟨sg34995,True.intro,True.intro⟩,True.intro⟩,⟨sg34998,True.intro,True.intro⟩⟩⟩,⟨sg35005,⟨sg35002,⟨sg35001,⟨sg35000,True.intro,True.intro⟩,True.intro⟩,⟨sg35004,⟨sg35003,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35008,⟨sg35007,⟨sg35006,True.intro,True.intro⟩,True.intro⟩,⟨sg35009,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_271All : degreeTree62_271.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35021,⟨sg35016,⟨sg35013,⟨sg35012,⟨sg35011,True.intro,True.intro⟩,True.intro⟩,⟨sg35015,⟨sg35014,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35019,⟨sg35018,⟨sg35017,True.intro,True.intro⟩,True.intro⟩,⟨sg35020,True.intro,True.intro⟩⟩⟩,⟨sg35027,⟨sg35024,⟨sg35023,⟨sg35022,True.intro,True.intro⟩,True.intro⟩,⟨sg35026,⟨sg35025,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35030,⟨sg35029,⟨sg35028,True.intro,True.intro⟩,True.intro⟩,⟨sg35031,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_272All : degreeTree62_272.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35010,degreeTree62_270All,degreeTree62_271All⟩

lemma degreeTree62_273All : degreeTree62_273.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35043,⟨sg35038,⟨sg35035,⟨sg35034,⟨sg35033,True.intro,True.intro⟩,True.intro⟩,⟨sg35037,⟨sg35036,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35041,⟨sg35040,⟨sg35039,True.intro,True.intro⟩,True.intro⟩,⟨sg35042,True.intro,True.intro⟩⟩⟩,⟨sg35049,⟨sg35046,⟨sg35045,⟨sg35044,True.intro,True.intro⟩,True.intro⟩,⟨sg35048,⟨sg35047,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35052,⟨sg35051,⟨sg35050,True.intro,True.intro⟩,True.intro⟩,⟨sg35053,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_274All : degreeTree62_274.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35065,⟨sg35060,⟨sg35057,⟨sg35056,⟨sg35055,True.intro,True.intro⟩,True.intro⟩,⟨sg35059,⟨sg35058,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35063,⟨sg35062,⟨sg35061,True.intro,True.intro⟩,True.intro⟩,⟨sg35064,True.intro,True.intro⟩⟩⟩,⟨sg35071,⟨sg35068,⟨sg35067,⟨sg35066,True.intro,True.intro⟩,True.intro⟩,⟨sg35070,⟨sg35069,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35074,⟨sg35073,⟨sg35072,True.intro,True.intro⟩,True.intro⟩,⟨sg35075,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_275All : degreeTree62_275.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35054,degreeTree62_273All,degreeTree62_274All⟩

lemma degreeTree62_276All : degreeTree62_276.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35032,degreeTree62_272All,degreeTree62_275All⟩

lemma degreeTree62_277All : degreeTree62_277.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35087,⟨sg35082,⟨sg35079,⟨sg35078,⟨sg35077,True.intro,True.intro⟩,True.intro⟩,⟨sg35081,⟨sg35080,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35085,⟨sg35084,⟨sg35083,True.intro,True.intro⟩,True.intro⟩,⟨sg35086,True.intro,True.intro⟩⟩⟩,⟨sg35093,⟨sg35090,⟨sg35089,⟨sg35088,True.intro,True.intro⟩,True.intro⟩,⟨sg35092,⟨sg35091,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35096,⟨sg35095,⟨sg35094,True.intro,True.intro⟩,True.intro⟩,⟨sg35097,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_278All : degreeTree62_278.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35109,⟨sg35104,⟨sg35101,⟨sg35100,⟨sg35099,True.intro,True.intro⟩,True.intro⟩,⟨sg35103,⟨sg35102,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35107,⟨sg35106,⟨sg35105,True.intro,True.intro⟩,True.intro⟩,⟨sg35108,True.intro,True.intro⟩⟩⟩,⟨sg35115,⟨sg35112,⟨sg35111,⟨sg35110,True.intro,True.intro⟩,True.intro⟩,⟨sg35114,⟨sg35113,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35118,⟨sg35117,⟨sg35116,True.intro,True.intro⟩,True.intro⟩,⟨sg35119,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_279All : degreeTree62_279.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35098,degreeTree62_277All,degreeTree62_278All⟩

lemma degreeTree62_280All : degreeTree62_280.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35131,⟨sg35126,⟨sg35123,⟨sg35122,⟨sg35121,True.intro,True.intro⟩,True.intro⟩,⟨sg35125,⟨sg35124,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35129,⟨sg35128,⟨sg35127,True.intro,True.intro⟩,True.intro⟩,⟨sg35130,True.intro,True.intro⟩⟩⟩,⟨sg35137,⟨sg35134,⟨sg35133,⟨sg35132,True.intro,True.intro⟩,True.intro⟩,⟨sg35136,⟨sg35135,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35140,⟨sg35139,⟨sg35138,True.intro,True.intro⟩,True.intro⟩,⟨sg35141,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_281All : degreeTree62_281.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35153,⟨sg35148,⟨sg35145,⟨sg35144,⟨sg35143,True.intro,True.intro⟩,True.intro⟩,⟨sg35147,⟨sg35146,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35151,⟨sg35150,⟨sg35149,True.intro,True.intro⟩,True.intro⟩,⟨sg35152,True.intro,True.intro⟩⟩⟩,⟨sg35158,⟨sg35156,⟨sg35155,⟨sg35154,True.intro,True.intro⟩,True.intro⟩,⟨sg35157,True.intro,True.intro⟩⟩,⟨sg35161,⟨sg35160,⟨sg35159,True.intro,True.intro⟩,True.intro⟩,⟨sg35162,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_282All : degreeTree62_282.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35142,degreeTree62_280All,degreeTree62_281All⟩

lemma degreeTree62_283All : degreeTree62_283.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35120,degreeTree62_279All,degreeTree62_282All⟩

lemma degreeTree62_284All : degreeTree62_284.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35076,degreeTree62_276All,degreeTree62_283All⟩

lemma degreeTree62_285All : degreeTree62_285.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34988,degreeTree62_269All,degreeTree62_284All⟩

lemma degreeTree62_286All : degreeTree62_286.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35174,⟨sg35169,⟨sg35166,⟨sg35165,⟨sg35164,True.intro,True.intro⟩,True.intro⟩,⟨sg35168,⟨sg35167,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35172,⟨sg35171,⟨sg35170,True.intro,True.intro⟩,True.intro⟩,⟨sg35173,True.intro,True.intro⟩⟩⟩,⟨sg35180,⟨sg35177,⟨sg35176,⟨sg35175,True.intro,True.intro⟩,True.intro⟩,⟨sg35179,⟨sg35178,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35183,⟨sg35182,⟨sg35181,True.intro,True.intro⟩,True.intro⟩,⟨sg35184,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_287All : degreeTree62_287.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35196,⟨sg35191,⟨sg35188,⟨sg35187,⟨sg35186,True.intro,True.intro⟩,True.intro⟩,⟨sg35190,⟨sg35189,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35194,⟨sg35193,⟨sg35192,True.intro,True.intro⟩,True.intro⟩,⟨sg35195,True.intro,True.intro⟩⟩⟩,⟨sg35202,⟨sg35199,⟨sg35198,⟨sg35197,True.intro,True.intro⟩,True.intro⟩,⟨sg35201,⟨sg35200,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35205,⟨sg35204,⟨sg35203,True.intro,True.intro⟩,True.intro⟩,⟨sg35206,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_288All : degreeTree62_288.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35185,degreeTree62_286All,degreeTree62_287All⟩

lemma degreeTree62_289All : degreeTree62_289.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35218,⟨sg35213,⟨sg35210,⟨sg35209,⟨sg35208,True.intro,True.intro⟩,True.intro⟩,⟨sg35212,⟨sg35211,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35216,⟨sg35215,⟨sg35214,True.intro,True.intro⟩,True.intro⟩,⟨sg35217,True.intro,True.intro⟩⟩⟩,⟨sg35224,⟨sg35221,⟨sg35220,⟨sg35219,True.intro,True.intro⟩,True.intro⟩,⟨sg35223,⟨sg35222,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35227,⟨sg35226,⟨sg35225,True.intro,True.intro⟩,True.intro⟩,⟨sg35228,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_290All : degreeTree62_290.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35240,⟨sg35235,⟨sg35232,⟨sg35231,⟨sg35230,True.intro,True.intro⟩,True.intro⟩,⟨sg35234,⟨sg35233,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35238,⟨sg35237,⟨sg35236,True.intro,True.intro⟩,True.intro⟩,⟨sg35239,True.intro,True.intro⟩⟩⟩,⟨sg35246,⟨sg35243,⟨sg35242,⟨sg35241,True.intro,True.intro⟩,True.intro⟩,⟨sg35245,⟨sg35244,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35249,⟨sg35248,⟨sg35247,True.intro,True.intro⟩,True.intro⟩,⟨sg35250,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_291All : degreeTree62_291.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35229,degreeTree62_289All,degreeTree62_290All⟩

lemma degreeTree62_292All : degreeTree62_292.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35207,degreeTree62_288All,degreeTree62_291All⟩

lemma degreeTree62_293All : degreeTree62_293.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35262,⟨sg35257,⟨sg35254,⟨sg35253,⟨sg35252,True.intro,True.intro⟩,True.intro⟩,⟨sg35256,⟨sg35255,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35260,⟨sg35259,⟨sg35258,True.intro,True.intro⟩,True.intro⟩,⟨sg35261,True.intro,True.intro⟩⟩⟩,⟨sg35268,⟨sg35265,⟨sg35264,⟨sg35263,True.intro,True.intro⟩,True.intro⟩,⟨sg35267,⟨sg35266,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35271,⟨sg35270,⟨sg35269,True.intro,True.intro⟩,True.intro⟩,⟨sg35272,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_294All : degreeTree62_294.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35284,⟨sg35279,⟨sg35276,⟨sg35275,⟨sg35274,True.intro,True.intro⟩,True.intro⟩,⟨sg35278,⟨sg35277,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35282,⟨sg35281,⟨sg35280,True.intro,True.intro⟩,True.intro⟩,⟨sg35283,True.intro,True.intro⟩⟩⟩,⟨sg35290,⟨sg35287,⟨sg35286,⟨sg35285,True.intro,True.intro⟩,True.intro⟩,⟨sg35289,⟨sg35288,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35293,⟨sg35292,⟨sg35291,True.intro,True.intro⟩,True.intro⟩,⟨sg35294,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_295All : degreeTree62_295.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35273,degreeTree62_293All,degreeTree62_294All⟩

lemma degreeTree62_296All : degreeTree62_296.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35306,⟨sg35301,⟨sg35298,⟨sg35297,⟨sg35296,True.intro,True.intro⟩,True.intro⟩,⟨sg35300,⟨sg35299,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35304,⟨sg35303,⟨sg35302,True.intro,True.intro⟩,True.intro⟩,⟨sg35305,True.intro,True.intro⟩⟩⟩,⟨sg35312,⟨sg35309,⟨sg35308,⟨sg35307,True.intro,True.intro⟩,True.intro⟩,⟨sg35311,⟨sg35310,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35315,⟨sg35314,⟨sg35313,True.intro,True.intro⟩,True.intro⟩,⟨sg35316,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_297All : degreeTree62_297.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35328,⟨sg35323,⟨sg35320,⟨sg35319,⟨sg35318,True.intro,True.intro⟩,True.intro⟩,⟨sg35322,⟨sg35321,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35326,⟨sg35325,⟨sg35324,True.intro,True.intro⟩,True.intro⟩,⟨sg35327,True.intro,True.intro⟩⟩⟩,⟨sg35334,⟨sg35331,⟨sg35330,⟨sg35329,True.intro,True.intro⟩,True.intro⟩,⟨sg35333,⟨sg35332,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35337,⟨sg35336,⟨sg35335,True.intro,True.intro⟩,True.intro⟩,⟨sg35338,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_298All : degreeTree62_298.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35317,degreeTree62_296All,degreeTree62_297All⟩

lemma degreeTree62_299All : degreeTree62_299.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35295,degreeTree62_295All,degreeTree62_298All⟩

lemma degreeTree62_300All : degreeTree62_300.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35251,degreeTree62_292All,degreeTree62_299All⟩

lemma degreeTree62_301All : degreeTree62_301.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35350,⟨sg35345,⟨sg35342,⟨sg35341,⟨sg35340,True.intro,True.intro⟩,True.intro⟩,⟨sg35344,⟨sg35343,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35348,⟨sg35347,⟨sg35346,True.intro,True.intro⟩,True.intro⟩,⟨sg35349,True.intro,True.intro⟩⟩⟩,⟨sg35356,⟨sg35353,⟨sg35352,⟨sg35351,True.intro,True.intro⟩,True.intro⟩,⟨sg35355,⟨sg35354,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35359,⟨sg35358,⟨sg35357,True.intro,True.intro⟩,True.intro⟩,⟨sg35360,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_302All : degreeTree62_302.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35372,⟨sg35367,⟨sg35364,⟨sg35363,⟨sg35362,True.intro,True.intro⟩,True.intro⟩,⟨sg35366,⟨sg35365,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35370,⟨sg35369,⟨sg35368,True.intro,True.intro⟩,True.intro⟩,⟨sg35371,True.intro,True.intro⟩⟩⟩,⟨sg35378,⟨sg35375,⟨sg35374,⟨sg35373,True.intro,True.intro⟩,True.intro⟩,⟨sg35377,⟨sg35376,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35381,⟨sg35380,⟨sg35379,True.intro,True.intro⟩,True.intro⟩,⟨sg35382,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_303All : degreeTree62_303.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35361,degreeTree62_301All,degreeTree62_302All⟩

lemma degreeTree62_304All : degreeTree62_304.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35394,⟨sg35389,⟨sg35386,⟨sg35385,⟨sg35384,True.intro,True.intro⟩,True.intro⟩,⟨sg35388,⟨sg35387,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35392,⟨sg35391,⟨sg35390,True.intro,True.intro⟩,True.intro⟩,⟨sg35393,True.intro,True.intro⟩⟩⟩,⟨sg35400,⟨sg35397,⟨sg35396,⟨sg35395,True.intro,True.intro⟩,True.intro⟩,⟨sg35399,⟨sg35398,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35403,⟨sg35402,⟨sg35401,True.intro,True.intro⟩,True.intro⟩,⟨sg35404,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_305All : degreeTree62_305.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35416,⟨sg35411,⟨sg35408,⟨sg35407,⟨sg35406,True.intro,True.intro⟩,True.intro⟩,⟨sg35410,⟨sg35409,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35414,⟨sg35413,⟨sg35412,True.intro,True.intro⟩,True.intro⟩,⟨sg35415,True.intro,True.intro⟩⟩⟩,⟨sg35422,⟨sg35419,⟨sg35418,⟨sg35417,True.intro,True.intro⟩,True.intro⟩,⟨sg35421,⟨sg35420,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35425,⟨sg35424,⟨sg35423,True.intro,True.intro⟩,True.intro⟩,⟨sg35426,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_306All : degreeTree62_306.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35405,degreeTree62_304All,degreeTree62_305All⟩

lemma degreeTree62_307All : degreeTree62_307.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35383,degreeTree62_303All,degreeTree62_306All⟩

lemma degreeTree62_308All : degreeTree62_308.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35438,⟨sg35433,⟨sg35430,⟨sg35429,⟨sg35428,True.intro,True.intro⟩,True.intro⟩,⟨sg35432,⟨sg35431,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35436,⟨sg35435,⟨sg35434,True.intro,True.intro⟩,True.intro⟩,⟨sg35437,True.intro,True.intro⟩⟩⟩,⟨sg35444,⟨sg35441,⟨sg35440,⟨sg35439,True.intro,True.intro⟩,True.intro⟩,⟨sg35443,⟨sg35442,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35447,⟨sg35446,⟨sg35445,True.intro,True.intro⟩,True.intro⟩,⟨sg35448,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_309All : degreeTree62_309.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35460,⟨sg35455,⟨sg35452,⟨sg35451,⟨sg35450,True.intro,True.intro⟩,True.intro⟩,⟨sg35454,⟨sg35453,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35458,⟨sg35457,⟨sg35456,True.intro,True.intro⟩,True.intro⟩,⟨sg35459,True.intro,True.intro⟩⟩⟩,⟨sg35466,⟨sg35463,⟨sg35462,⟨sg35461,True.intro,True.intro⟩,True.intro⟩,⟨sg35465,⟨sg35464,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35469,⟨sg35468,⟨sg35467,True.intro,True.intro⟩,True.intro⟩,⟨sg35470,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_310All : degreeTree62_310.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35449,degreeTree62_308All,degreeTree62_309All⟩

lemma degreeTree62_311All : degreeTree62_311.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35482,⟨sg35477,⟨sg35474,⟨sg35473,⟨sg35472,True.intro,True.intro⟩,True.intro⟩,⟨sg35476,⟨sg35475,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35480,⟨sg35479,⟨sg35478,True.intro,True.intro⟩,True.intro⟩,⟨sg35481,True.intro,True.intro⟩⟩⟩,⟨sg35488,⟨sg35485,⟨sg35484,⟨sg35483,True.intro,True.intro⟩,True.intro⟩,⟨sg35487,⟨sg35486,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35491,⟨sg35490,⟨sg35489,True.intro,True.intro⟩,True.intro⟩,⟨sg35492,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_312All : degreeTree62_312.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35504,⟨sg35499,⟨sg35496,⟨sg35495,⟨sg35494,True.intro,True.intro⟩,True.intro⟩,⟨sg35498,⟨sg35497,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35502,⟨sg35501,⟨sg35500,True.intro,True.intro⟩,True.intro⟩,⟨sg35503,True.intro,True.intro⟩⟩⟩,⟨sg35509,⟨sg35507,⟨sg35506,⟨sg35505,True.intro,True.intro⟩,True.intro⟩,⟨sg35508,True.intro,True.intro⟩⟩,⟨sg35512,⟨sg35511,⟨sg35510,True.intro,True.intro⟩,True.intro⟩,⟨sg35513,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_313All : degreeTree62_313.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35493,degreeTree62_311All,degreeTree62_312All⟩

lemma degreeTree62_314All : degreeTree62_314.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35471,degreeTree62_310All,degreeTree62_313All⟩

lemma degreeTree62_315All : degreeTree62_315.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35427,degreeTree62_307All,degreeTree62_314All⟩

lemma degreeTree62_316All : degreeTree62_316.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35339,degreeTree62_300All,degreeTree62_315All⟩

lemma degreeTree62_317All : degreeTree62_317.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35163,degreeTree62_285All,degreeTree62_316All⟩

lemma degreeTree62_318All : degreeTree62_318.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35525,⟨sg35520,⟨sg35517,⟨sg35516,⟨sg35515,True.intro,True.intro⟩,True.intro⟩,⟨sg35519,⟨sg35518,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35523,⟨sg35522,⟨sg35521,True.intro,True.intro⟩,True.intro⟩,⟨sg35524,True.intro,True.intro⟩⟩⟩,⟨sg35531,⟨sg35528,⟨sg35527,⟨sg35526,True.intro,True.intro⟩,True.intro⟩,⟨sg35530,⟨sg35529,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35534,⟨sg35533,⟨sg35532,True.intro,True.intro⟩,True.intro⟩,⟨sg35535,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_319All : degreeTree62_319.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35547,⟨sg35542,⟨sg35539,⟨sg35538,⟨sg35537,True.intro,True.intro⟩,True.intro⟩,⟨sg35541,⟨sg35540,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35545,⟨sg35544,⟨sg35543,True.intro,True.intro⟩,True.intro⟩,⟨sg35546,True.intro,True.intro⟩⟩⟩,⟨sg35553,⟨sg35550,⟨sg35549,⟨sg35548,True.intro,True.intro⟩,True.intro⟩,⟨sg35552,⟨sg35551,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35556,⟨sg35555,⟨sg35554,True.intro,True.intro⟩,True.intro⟩,⟨sg35557,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_320All : degreeTree62_320.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35536,degreeTree62_318All,degreeTree62_319All⟩

lemma degreeTree62_321All : degreeTree62_321.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35569,⟨sg35564,⟨sg35561,⟨sg35560,⟨sg35559,True.intro,True.intro⟩,True.intro⟩,⟨sg35563,⟨sg35562,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35567,⟨sg35566,⟨sg35565,True.intro,True.intro⟩,True.intro⟩,⟨sg35568,True.intro,True.intro⟩⟩⟩,⟨sg35575,⟨sg35572,⟨sg35571,⟨sg35570,True.intro,True.intro⟩,True.intro⟩,⟨sg35574,⟨sg35573,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35578,⟨sg35577,⟨sg35576,True.intro,True.intro⟩,True.intro⟩,⟨sg35579,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_322All : degreeTree62_322.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35591,⟨sg35586,⟨sg35583,⟨sg35582,⟨sg35581,True.intro,True.intro⟩,True.intro⟩,⟨sg35585,⟨sg35584,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35589,⟨sg35588,⟨sg35587,True.intro,True.intro⟩,True.intro⟩,⟨sg35590,True.intro,True.intro⟩⟩⟩,⟨sg35597,⟨sg35594,⟨sg35593,⟨sg35592,True.intro,True.intro⟩,True.intro⟩,⟨sg35596,⟨sg35595,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35600,⟨sg35599,⟨sg35598,True.intro,True.intro⟩,True.intro⟩,⟨sg35601,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_323All : degreeTree62_323.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35580,degreeTree62_321All,degreeTree62_322All⟩

lemma degreeTree62_324All : degreeTree62_324.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35558,degreeTree62_320All,degreeTree62_323All⟩

lemma degreeTree62_325All : degreeTree62_325.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35613,⟨sg35608,⟨sg35605,⟨sg35604,⟨sg35603,True.intro,True.intro⟩,True.intro⟩,⟨sg35607,⟨sg35606,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35611,⟨sg35610,⟨sg35609,True.intro,True.intro⟩,True.intro⟩,⟨sg35612,True.intro,True.intro⟩⟩⟩,⟨sg35619,⟨sg35616,⟨sg35615,⟨sg35614,True.intro,True.intro⟩,True.intro⟩,⟨sg35618,⟨sg35617,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35622,⟨sg35621,⟨sg35620,True.intro,True.intro⟩,True.intro⟩,⟨sg35623,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_326All : degreeTree62_326.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35635,⟨sg35630,⟨sg35627,⟨sg35626,⟨sg35625,True.intro,True.intro⟩,True.intro⟩,⟨sg35629,⟨sg35628,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35633,⟨sg35632,⟨sg35631,True.intro,True.intro⟩,True.intro⟩,⟨sg35634,True.intro,True.intro⟩⟩⟩,⟨sg35641,⟨sg35638,⟨sg35637,⟨sg35636,True.intro,True.intro⟩,True.intro⟩,⟨sg35640,⟨sg35639,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35644,⟨sg35643,⟨sg35642,True.intro,True.intro⟩,True.intro⟩,⟨sg35645,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_327All : degreeTree62_327.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35624,degreeTree62_325All,degreeTree62_326All⟩

lemma degreeTree62_328All : degreeTree62_328.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35657,⟨sg35652,⟨sg35649,⟨sg35648,⟨sg35647,True.intro,True.intro⟩,True.intro⟩,⟨sg35651,⟨sg35650,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35655,⟨sg35654,⟨sg35653,True.intro,True.intro⟩,True.intro⟩,⟨sg35656,True.intro,True.intro⟩⟩⟩,⟨sg35663,⟨sg35660,⟨sg35659,⟨sg35658,True.intro,True.intro⟩,True.intro⟩,⟨sg35662,⟨sg35661,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35666,⟨sg35665,⟨sg35664,True.intro,True.intro⟩,True.intro⟩,⟨sg35667,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_329All : degreeTree62_329.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35679,⟨sg35674,⟨sg35671,⟨sg35670,⟨sg35669,True.intro,True.intro⟩,True.intro⟩,⟨sg35673,⟨sg35672,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35677,⟨sg35676,⟨sg35675,True.intro,True.intro⟩,True.intro⟩,⟨sg35678,True.intro,True.intro⟩⟩⟩,⟨sg35685,⟨sg35682,⟨sg35681,⟨sg35680,True.intro,True.intro⟩,True.intro⟩,⟨sg35684,⟨sg35683,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35688,⟨sg35687,⟨sg35686,True.intro,True.intro⟩,True.intro⟩,⟨sg35689,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_330All : degreeTree62_330.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35668,degreeTree62_328All,degreeTree62_329All⟩

lemma degreeTree62_331All : degreeTree62_331.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35646,degreeTree62_327All,degreeTree62_330All⟩

lemma degreeTree62_332All : degreeTree62_332.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35602,degreeTree62_324All,degreeTree62_331All⟩

lemma degreeTree62_333All : degreeTree62_333.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35701,⟨sg35696,⟨sg35693,⟨sg35692,⟨sg35691,True.intro,True.intro⟩,True.intro⟩,⟨sg35695,⟨sg35694,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35699,⟨sg35698,⟨sg35697,True.intro,True.intro⟩,True.intro⟩,⟨sg35700,True.intro,True.intro⟩⟩⟩,⟨sg35707,⟨sg35704,⟨sg35703,⟨sg35702,True.intro,True.intro⟩,True.intro⟩,⟨sg35706,⟨sg35705,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35710,⟨sg35709,⟨sg35708,True.intro,True.intro⟩,True.intro⟩,⟨sg35711,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_334All : degreeTree62_334.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35723,⟨sg35718,⟨sg35715,⟨sg35714,⟨sg35713,True.intro,True.intro⟩,True.intro⟩,⟨sg35717,⟨sg35716,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35721,⟨sg35720,⟨sg35719,True.intro,True.intro⟩,True.intro⟩,⟨sg35722,True.intro,True.intro⟩⟩⟩,⟨sg35729,⟨sg35726,⟨sg35725,⟨sg35724,True.intro,True.intro⟩,True.intro⟩,⟨sg35728,⟨sg35727,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35732,⟨sg35731,⟨sg35730,True.intro,True.intro⟩,True.intro⟩,⟨sg35733,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_335All : degreeTree62_335.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35712,degreeTree62_333All,degreeTree62_334All⟩

lemma degreeTree62_336All : degreeTree62_336.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35745,⟨sg35740,⟨sg35737,⟨sg35736,⟨sg35735,True.intro,True.intro⟩,True.intro⟩,⟨sg35739,⟨sg35738,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35743,⟨sg35742,⟨sg35741,True.intro,True.intro⟩,True.intro⟩,⟨sg35744,True.intro,True.intro⟩⟩⟩,⟨sg35751,⟨sg35748,⟨sg35747,⟨sg35746,True.intro,True.intro⟩,True.intro⟩,⟨sg35750,⟨sg35749,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35754,⟨sg35753,⟨sg35752,True.intro,True.intro⟩,True.intro⟩,⟨sg35755,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_337All : degreeTree62_337.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35767,⟨sg35762,⟨sg35759,⟨sg35758,⟨sg35757,True.intro,True.intro⟩,True.intro⟩,⟨sg35761,⟨sg35760,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35765,⟨sg35764,⟨sg35763,True.intro,True.intro⟩,True.intro⟩,⟨sg35766,True.intro,True.intro⟩⟩⟩,⟨sg35773,⟨sg35770,⟨sg35769,⟨sg35768,True.intro,True.intro⟩,True.intro⟩,⟨sg35772,⟨sg35771,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35776,⟨sg35775,⟨sg35774,True.intro,True.intro⟩,True.intro⟩,⟨sg35777,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_338All : degreeTree62_338.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35756,degreeTree62_336All,degreeTree62_337All⟩

lemma degreeTree62_339All : degreeTree62_339.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35734,degreeTree62_335All,degreeTree62_338All⟩

lemma degreeTree62_340All : degreeTree62_340.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35789,⟨sg35784,⟨sg35781,⟨sg35780,⟨sg35779,True.intro,True.intro⟩,True.intro⟩,⟨sg35783,⟨sg35782,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35787,⟨sg35786,⟨sg35785,True.intro,True.intro⟩,True.intro⟩,⟨sg35788,True.intro,True.intro⟩⟩⟩,⟨sg35795,⟨sg35792,⟨sg35791,⟨sg35790,True.intro,True.intro⟩,True.intro⟩,⟨sg35794,⟨sg35793,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35798,⟨sg35797,⟨sg35796,True.intro,True.intro⟩,True.intro⟩,⟨sg35799,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_341All : degreeTree62_341.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35811,⟨sg35806,⟨sg35803,⟨sg35802,⟨sg35801,True.intro,True.intro⟩,True.intro⟩,⟨sg35805,⟨sg35804,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35809,⟨sg35808,⟨sg35807,True.intro,True.intro⟩,True.intro⟩,⟨sg35810,True.intro,True.intro⟩⟩⟩,⟨sg35817,⟨sg35814,⟨sg35813,⟨sg35812,True.intro,True.intro⟩,True.intro⟩,⟨sg35816,⟨sg35815,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35820,⟨sg35819,⟨sg35818,True.intro,True.intro⟩,True.intro⟩,⟨sg35821,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_342All : degreeTree62_342.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35800,degreeTree62_340All,degreeTree62_341All⟩

lemma degreeTree62_343All : degreeTree62_343.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35833,⟨sg35828,⟨sg35825,⟨sg35824,⟨sg35823,True.intro,True.intro⟩,True.intro⟩,⟨sg35827,⟨sg35826,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35831,⟨sg35830,⟨sg35829,True.intro,True.intro⟩,True.intro⟩,⟨sg35832,True.intro,True.intro⟩⟩⟩,⟨sg35839,⟨sg35836,⟨sg35835,⟨sg35834,True.intro,True.intro⟩,True.intro⟩,⟨sg35838,⟨sg35837,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35842,⟨sg35841,⟨sg35840,True.intro,True.intro⟩,True.intro⟩,⟨sg35843,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_344All : degreeTree62_344.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35855,⟨sg35850,⟨sg35847,⟨sg35846,⟨sg35845,True.intro,True.intro⟩,True.intro⟩,⟨sg35849,⟨sg35848,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35853,⟨sg35852,⟨sg35851,True.intro,True.intro⟩,True.intro⟩,⟨sg35854,True.intro,True.intro⟩⟩⟩,⟨sg35860,⟨sg35858,⟨sg35857,⟨sg35856,True.intro,True.intro⟩,True.intro⟩,⟨sg35859,True.intro,True.intro⟩⟩,⟨sg35863,⟨sg35862,⟨sg35861,True.intro,True.intro⟩,True.intro⟩,⟨sg35864,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_345All : degreeTree62_345.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35844,degreeTree62_343All,degreeTree62_344All⟩

lemma degreeTree62_346All : degreeTree62_346.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35822,degreeTree62_342All,degreeTree62_345All⟩

lemma degreeTree62_347All : degreeTree62_347.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35778,degreeTree62_339All,degreeTree62_346All⟩

lemma degreeTree62_348All : degreeTree62_348.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35690,degreeTree62_332All,degreeTree62_347All⟩

lemma degreeTree62_349All : degreeTree62_349.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35876,⟨sg35871,⟨sg35868,⟨sg35867,⟨sg35866,True.intro,True.intro⟩,True.intro⟩,⟨sg35870,⟨sg35869,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35874,⟨sg35873,⟨sg35872,True.intro,True.intro⟩,True.intro⟩,⟨sg35875,True.intro,True.intro⟩⟩⟩,⟨sg35882,⟨sg35879,⟨sg35878,⟨sg35877,True.intro,True.intro⟩,True.intro⟩,⟨sg35881,⟨sg35880,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35885,⟨sg35884,⟨sg35883,True.intro,True.intro⟩,True.intro⟩,⟨sg35886,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_350All : degreeTree62_350.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35898,⟨sg35893,⟨sg35890,⟨sg35889,⟨sg35888,True.intro,True.intro⟩,True.intro⟩,⟨sg35892,⟨sg35891,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35896,⟨sg35895,⟨sg35894,True.intro,True.intro⟩,True.intro⟩,⟨sg35897,True.intro,True.intro⟩⟩⟩,⟨sg35904,⟨sg35901,⟨sg35900,⟨sg35899,True.intro,True.intro⟩,True.intro⟩,⟨sg35903,⟨sg35902,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35907,⟨sg35906,⟨sg35905,True.intro,True.intro⟩,True.intro⟩,⟨sg35908,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_351All : degreeTree62_351.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35887,degreeTree62_349All,degreeTree62_350All⟩

lemma degreeTree62_352All : degreeTree62_352.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35920,⟨sg35915,⟨sg35912,⟨sg35911,⟨sg35910,True.intro,True.intro⟩,True.intro⟩,⟨sg35914,⟨sg35913,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35918,⟨sg35917,⟨sg35916,True.intro,True.intro⟩,True.intro⟩,⟨sg35919,True.intro,True.intro⟩⟩⟩,⟨sg35926,⟨sg35923,⟨sg35922,⟨sg35921,True.intro,True.intro⟩,True.intro⟩,⟨sg35925,⟨sg35924,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35929,⟨sg35928,⟨sg35927,True.intro,True.intro⟩,True.intro⟩,⟨sg35930,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_353All : degreeTree62_353.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35942,⟨sg35937,⟨sg35934,⟨sg35933,⟨sg35932,True.intro,True.intro⟩,True.intro⟩,⟨sg35936,⟨sg35935,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35940,⟨sg35939,⟨sg35938,True.intro,True.intro⟩,True.intro⟩,⟨sg35941,True.intro,True.intro⟩⟩⟩,⟨sg35948,⟨sg35945,⟨sg35944,⟨sg35943,True.intro,True.intro⟩,True.intro⟩,⟨sg35947,⟨sg35946,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35951,⟨sg35950,⟨sg35949,True.intro,True.intro⟩,True.intro⟩,⟨sg35952,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_354All : degreeTree62_354.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35931,degreeTree62_352All,degreeTree62_353All⟩

lemma degreeTree62_355All : degreeTree62_355.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35909,degreeTree62_351All,degreeTree62_354All⟩

lemma degreeTree62_356All : degreeTree62_356.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35964,⟨sg35959,⟨sg35956,⟨sg35955,⟨sg35954,True.intro,True.intro⟩,True.intro⟩,⟨sg35958,⟨sg35957,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35962,⟨sg35961,⟨sg35960,True.intro,True.intro⟩,True.intro⟩,⟨sg35963,True.intro,True.intro⟩⟩⟩,⟨sg35970,⟨sg35967,⟨sg35966,⟨sg35965,True.intro,True.intro⟩,True.intro⟩,⟨sg35969,⟨sg35968,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35973,⟨sg35972,⟨sg35971,True.intro,True.intro⟩,True.intro⟩,⟨sg35974,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_357All : degreeTree62_357.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35986,⟨sg35981,⟨sg35978,⟨sg35977,⟨sg35976,True.intro,True.intro⟩,True.intro⟩,⟨sg35980,⟨sg35979,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35984,⟨sg35983,⟨sg35982,True.intro,True.intro⟩,True.intro⟩,⟨sg35985,True.intro,True.intro⟩⟩⟩,⟨sg35992,⟨sg35989,⟨sg35988,⟨sg35987,True.intro,True.intro⟩,True.intro⟩,⟨sg35991,⟨sg35990,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg35995,⟨sg35994,⟨sg35993,True.intro,True.intro⟩,True.intro⟩,⟨sg35996,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_358All : degreeTree62_358.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35975,degreeTree62_356All,degreeTree62_357All⟩

lemma degreeTree62_359All : degreeTree62_359.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36008,⟨sg36003,⟨sg36000,⟨sg35999,⟨sg35998,True.intro,True.intro⟩,True.intro⟩,⟨sg36002,⟨sg36001,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36006,⟨sg36005,⟨sg36004,True.intro,True.intro⟩,True.intro⟩,⟨sg36007,True.intro,True.intro⟩⟩⟩,⟨sg36014,⟨sg36011,⟨sg36010,⟨sg36009,True.intro,True.intro⟩,True.intro⟩,⟨sg36013,⟨sg36012,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36017,⟨sg36016,⟨sg36015,True.intro,True.intro⟩,True.intro⟩,⟨sg36018,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_360All : degreeTree62_360.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36030,⟨sg36025,⟨sg36022,⟨sg36021,⟨sg36020,True.intro,True.intro⟩,True.intro⟩,⟨sg36024,⟨sg36023,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36028,⟨sg36027,⟨sg36026,True.intro,True.intro⟩,True.intro⟩,⟨sg36029,True.intro,True.intro⟩⟩⟩,⟨sg36036,⟨sg36033,⟨sg36032,⟨sg36031,True.intro,True.intro⟩,True.intro⟩,⟨sg36035,⟨sg36034,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36039,⟨sg36038,⟨sg36037,True.intro,True.intro⟩,True.intro⟩,⟨sg36040,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_361All : degreeTree62_361.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36019,degreeTree62_359All,degreeTree62_360All⟩

lemma degreeTree62_362All : degreeTree62_362.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35997,degreeTree62_358All,degreeTree62_361All⟩

lemma degreeTree62_363All : degreeTree62_363.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35953,degreeTree62_355All,degreeTree62_362All⟩

lemma degreeTree62_364All : degreeTree62_364.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36052,⟨sg36047,⟨sg36044,⟨sg36043,⟨sg36042,True.intro,True.intro⟩,True.intro⟩,⟨sg36046,⟨sg36045,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36050,⟨sg36049,⟨sg36048,True.intro,True.intro⟩,True.intro⟩,⟨sg36051,True.intro,True.intro⟩⟩⟩,⟨sg36058,⟨sg36055,⟨sg36054,⟨sg36053,True.intro,True.intro⟩,True.intro⟩,⟨sg36057,⟨sg36056,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36061,⟨sg36060,⟨sg36059,True.intro,True.intro⟩,True.intro⟩,⟨sg36062,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_365All : degreeTree62_365.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36074,⟨sg36069,⟨sg36066,⟨sg36065,⟨sg36064,True.intro,True.intro⟩,True.intro⟩,⟨sg36068,⟨sg36067,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36072,⟨sg36071,⟨sg36070,True.intro,True.intro⟩,True.intro⟩,⟨sg36073,True.intro,True.intro⟩⟩⟩,⟨sg36080,⟨sg36077,⟨sg36076,⟨sg36075,True.intro,True.intro⟩,True.intro⟩,⟨sg36079,⟨sg36078,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36083,⟨sg36082,⟨sg36081,True.intro,True.intro⟩,True.intro⟩,⟨sg36084,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_366All : degreeTree62_366.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36063,degreeTree62_364All,degreeTree62_365All⟩

lemma degreeTree62_367All : degreeTree62_367.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36096,⟨sg36091,⟨sg36088,⟨sg36087,⟨sg36086,True.intro,True.intro⟩,True.intro⟩,⟨sg36090,⟨sg36089,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36094,⟨sg36093,⟨sg36092,True.intro,True.intro⟩,True.intro⟩,⟨sg36095,True.intro,True.intro⟩⟩⟩,⟨sg36102,⟨sg36099,⟨sg36098,⟨sg36097,True.intro,True.intro⟩,True.intro⟩,⟨sg36101,⟨sg36100,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36105,⟨sg36104,⟨sg36103,True.intro,True.intro⟩,True.intro⟩,⟨sg36106,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_368All : degreeTree62_368.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36118,⟨sg36113,⟨sg36110,⟨sg36109,⟨sg36108,True.intro,True.intro⟩,True.intro⟩,⟨sg36112,⟨sg36111,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36116,⟨sg36115,⟨sg36114,True.intro,True.intro⟩,True.intro⟩,⟨sg36117,True.intro,True.intro⟩⟩⟩,⟨sg36124,⟨sg36121,⟨sg36120,⟨sg36119,True.intro,True.intro⟩,True.intro⟩,⟨sg36123,⟨sg36122,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36127,⟨sg36126,⟨sg36125,True.intro,True.intro⟩,True.intro⟩,⟨sg36128,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_369All : degreeTree62_369.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36107,degreeTree62_367All,degreeTree62_368All⟩

lemma degreeTree62_370All : degreeTree62_370.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36085,degreeTree62_366All,degreeTree62_369All⟩

lemma degreeTree62_371All : degreeTree62_371.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36140,⟨sg36135,⟨sg36132,⟨sg36131,⟨sg36130,True.intro,True.intro⟩,True.intro⟩,⟨sg36134,⟨sg36133,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36138,⟨sg36137,⟨sg36136,True.intro,True.intro⟩,True.intro⟩,⟨sg36139,True.intro,True.intro⟩⟩⟩,⟨sg36146,⟨sg36143,⟨sg36142,⟨sg36141,True.intro,True.intro⟩,True.intro⟩,⟨sg36145,⟨sg36144,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36149,⟨sg36148,⟨sg36147,True.intro,True.intro⟩,True.intro⟩,⟨sg36150,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_372All : degreeTree62_372.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36162,⟨sg36157,⟨sg36154,⟨sg36153,⟨sg36152,True.intro,True.intro⟩,True.intro⟩,⟨sg36156,⟨sg36155,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36160,⟨sg36159,⟨sg36158,True.intro,True.intro⟩,True.intro⟩,⟨sg36161,True.intro,True.intro⟩⟩⟩,⟨sg36168,⟨sg36165,⟨sg36164,⟨sg36163,True.intro,True.intro⟩,True.intro⟩,⟨sg36167,⟨sg36166,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36171,⟨sg36170,⟨sg36169,True.intro,True.intro⟩,True.intro⟩,⟨sg36172,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_373All : degreeTree62_373.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36151,degreeTree62_371All,degreeTree62_372All⟩

lemma degreeTree62_374All : degreeTree62_374.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36184,⟨sg36179,⟨sg36176,⟨sg36175,⟨sg36174,True.intro,True.intro⟩,True.intro⟩,⟨sg36178,⟨sg36177,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36182,⟨sg36181,⟨sg36180,True.intro,True.intro⟩,True.intro⟩,⟨sg36183,True.intro,True.intro⟩⟩⟩,⟨sg36190,⟨sg36187,⟨sg36186,⟨sg36185,True.intro,True.intro⟩,True.intro⟩,⟨sg36189,⟨sg36188,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36193,⟨sg36192,⟨sg36191,True.intro,True.intro⟩,True.intro⟩,⟨sg36194,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_375All : degreeTree62_375.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36206,⟨sg36201,⟨sg36198,⟨sg36197,⟨sg36196,True.intro,True.intro⟩,True.intro⟩,⟨sg36200,⟨sg36199,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36204,⟨sg36203,⟨sg36202,True.intro,True.intro⟩,True.intro⟩,⟨sg36205,True.intro,True.intro⟩⟩⟩,⟨sg36211,⟨sg36209,⟨sg36208,⟨sg36207,True.intro,True.intro⟩,True.intro⟩,⟨sg36210,True.intro,True.intro⟩⟩,⟨sg36214,⟨sg36213,⟨sg36212,True.intro,True.intro⟩,True.intro⟩,⟨sg36215,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_376All : degreeTree62_376.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36195,degreeTree62_374All,degreeTree62_375All⟩

lemma degreeTree62_377All : degreeTree62_377.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36173,degreeTree62_373All,degreeTree62_376All⟩

lemma degreeTree62_378All : degreeTree62_378.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36129,degreeTree62_370All,degreeTree62_377All⟩

lemma degreeTree62_379All : degreeTree62_379.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36041,degreeTree62_363All,degreeTree62_378All⟩

lemma degreeTree62_380All : degreeTree62_380.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35865,degreeTree62_348All,degreeTree62_379All⟩

lemma degreeTree62_381All : degreeTree62_381.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg35514,degreeTree62_317All,degreeTree62_380All⟩

lemma degreeTree62_382All : degreeTree62_382.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36227,⟨sg36222,⟨sg36219,⟨sg36218,⟨sg36217,True.intro,True.intro⟩,True.intro⟩,⟨sg36221,⟨sg36220,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36225,⟨sg36224,⟨sg36223,True.intro,True.intro⟩,True.intro⟩,⟨sg36226,True.intro,True.intro⟩⟩⟩,⟨sg36233,⟨sg36230,⟨sg36229,⟨sg36228,True.intro,True.intro⟩,True.intro⟩,⟨sg36232,⟨sg36231,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36236,⟨sg36235,⟨sg36234,True.intro,True.intro⟩,True.intro⟩,⟨sg36237,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_383All : degreeTree62_383.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36249,⟨sg36244,⟨sg36241,⟨sg36240,⟨sg36239,True.intro,True.intro⟩,True.intro⟩,⟨sg36243,⟨sg36242,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36247,⟨sg36246,⟨sg36245,True.intro,True.intro⟩,True.intro⟩,⟨sg36248,True.intro,True.intro⟩⟩⟩,⟨sg36255,⟨sg36252,⟨sg36251,⟨sg36250,True.intro,True.intro⟩,True.intro⟩,⟨sg36254,⟨sg36253,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36258,⟨sg36257,⟨sg36256,True.intro,True.intro⟩,True.intro⟩,⟨sg36259,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_384All : degreeTree62_384.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36238,degreeTree62_382All,degreeTree62_383All⟩

lemma degreeTree62_385All : degreeTree62_385.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36271,⟨sg36266,⟨sg36263,⟨sg36262,⟨sg36261,True.intro,True.intro⟩,True.intro⟩,⟨sg36265,⟨sg36264,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36269,⟨sg36268,⟨sg36267,True.intro,True.intro⟩,True.intro⟩,⟨sg36270,True.intro,True.intro⟩⟩⟩,⟨sg36277,⟨sg36274,⟨sg36273,⟨sg36272,True.intro,True.intro⟩,True.intro⟩,⟨sg36276,⟨sg36275,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36280,⟨sg36279,⟨sg36278,True.intro,True.intro⟩,True.intro⟩,⟨sg36281,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_386All : degreeTree62_386.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36293,⟨sg36288,⟨sg36285,⟨sg36284,⟨sg36283,True.intro,True.intro⟩,True.intro⟩,⟨sg36287,⟨sg36286,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36291,⟨sg36290,⟨sg36289,True.intro,True.intro⟩,True.intro⟩,⟨sg36292,True.intro,True.intro⟩⟩⟩,⟨sg36299,⟨sg36296,⟨sg36295,⟨sg36294,True.intro,True.intro⟩,True.intro⟩,⟨sg36298,⟨sg36297,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36302,⟨sg36301,⟨sg36300,True.intro,True.intro⟩,True.intro⟩,⟨sg36303,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_387All : degreeTree62_387.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36282,degreeTree62_385All,degreeTree62_386All⟩

lemma degreeTree62_388All : degreeTree62_388.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36260,degreeTree62_384All,degreeTree62_387All⟩

lemma degreeTree62_389All : degreeTree62_389.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36315,⟨sg36310,⟨sg36307,⟨sg36306,⟨sg36305,True.intro,True.intro⟩,True.intro⟩,⟨sg36309,⟨sg36308,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36313,⟨sg36312,⟨sg36311,True.intro,True.intro⟩,True.intro⟩,⟨sg36314,True.intro,True.intro⟩⟩⟩,⟨sg36321,⟨sg36318,⟨sg36317,⟨sg36316,True.intro,True.intro⟩,True.intro⟩,⟨sg36320,⟨sg36319,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36324,⟨sg36323,⟨sg36322,True.intro,True.intro⟩,True.intro⟩,⟨sg36325,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_390All : degreeTree62_390.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36337,⟨sg36332,⟨sg36329,⟨sg36328,⟨sg36327,True.intro,True.intro⟩,True.intro⟩,⟨sg36331,⟨sg36330,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36335,⟨sg36334,⟨sg36333,True.intro,True.intro⟩,True.intro⟩,⟨sg36336,True.intro,True.intro⟩⟩⟩,⟨sg36343,⟨sg36340,⟨sg36339,⟨sg36338,True.intro,True.intro⟩,True.intro⟩,⟨sg36342,⟨sg36341,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36346,⟨sg36345,⟨sg36344,True.intro,True.intro⟩,True.intro⟩,⟨sg36347,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_391All : degreeTree62_391.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36326,degreeTree62_389All,degreeTree62_390All⟩

lemma degreeTree62_392All : degreeTree62_392.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36359,⟨sg36354,⟨sg36351,⟨sg36350,⟨sg36349,True.intro,True.intro⟩,True.intro⟩,⟨sg36353,⟨sg36352,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36357,⟨sg36356,⟨sg36355,True.intro,True.intro⟩,True.intro⟩,⟨sg36358,True.intro,True.intro⟩⟩⟩,⟨sg36365,⟨sg36362,⟨sg36361,⟨sg36360,True.intro,True.intro⟩,True.intro⟩,⟨sg36364,⟨sg36363,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36368,⟨sg36367,⟨sg36366,True.intro,True.intro⟩,True.intro⟩,⟨sg36369,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_393All : degreeTree62_393.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36381,⟨sg36376,⟨sg36373,⟨sg36372,⟨sg36371,True.intro,True.intro⟩,True.intro⟩,⟨sg36375,⟨sg36374,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36379,⟨sg36378,⟨sg36377,True.intro,True.intro⟩,True.intro⟩,⟨sg36380,True.intro,True.intro⟩⟩⟩,⟨sg36387,⟨sg36384,⟨sg36383,⟨sg36382,True.intro,True.intro⟩,True.intro⟩,⟨sg36386,⟨sg36385,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36390,⟨sg36389,⟨sg36388,True.intro,True.intro⟩,True.intro⟩,⟨sg36391,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_394All : degreeTree62_394.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36370,degreeTree62_392All,degreeTree62_393All⟩

lemma degreeTree62_395All : degreeTree62_395.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36348,degreeTree62_391All,degreeTree62_394All⟩

lemma degreeTree62_396All : degreeTree62_396.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36304,degreeTree62_388All,degreeTree62_395All⟩

lemma degreeTree62_397All : degreeTree62_397.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36403,⟨sg36398,⟨sg36395,⟨sg36394,⟨sg36393,True.intro,True.intro⟩,True.intro⟩,⟨sg36397,⟨sg36396,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36401,⟨sg36400,⟨sg36399,True.intro,True.intro⟩,True.intro⟩,⟨sg36402,True.intro,True.intro⟩⟩⟩,⟨sg36409,⟨sg36406,⟨sg36405,⟨sg36404,True.intro,True.intro⟩,True.intro⟩,⟨sg36408,⟨sg36407,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36412,⟨sg36411,⟨sg36410,True.intro,True.intro⟩,True.intro⟩,⟨sg36413,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_398All : degreeTree62_398.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36425,⟨sg36420,⟨sg36417,⟨sg36416,⟨sg36415,True.intro,True.intro⟩,True.intro⟩,⟨sg36419,⟨sg36418,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36423,⟨sg36422,⟨sg36421,True.intro,True.intro⟩,True.intro⟩,⟨sg36424,True.intro,True.intro⟩⟩⟩,⟨sg36431,⟨sg36428,⟨sg36427,⟨sg36426,True.intro,True.intro⟩,True.intro⟩,⟨sg36430,⟨sg36429,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36434,⟨sg36433,⟨sg36432,True.intro,True.intro⟩,True.intro⟩,⟨sg36435,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_399All : degreeTree62_399.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36414,degreeTree62_397All,degreeTree62_398All⟩

lemma degreeTree62_400All : degreeTree62_400.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36447,⟨sg36442,⟨sg36439,⟨sg36438,⟨sg36437,True.intro,True.intro⟩,True.intro⟩,⟨sg36441,⟨sg36440,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36445,⟨sg36444,⟨sg36443,True.intro,True.intro⟩,True.intro⟩,⟨sg36446,True.intro,True.intro⟩⟩⟩,⟨sg36453,⟨sg36450,⟨sg36449,⟨sg36448,True.intro,True.intro⟩,True.intro⟩,⟨sg36452,⟨sg36451,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36456,⟨sg36455,⟨sg36454,True.intro,True.intro⟩,True.intro⟩,⟨sg36457,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_401All : degreeTree62_401.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36469,⟨sg36464,⟨sg36461,⟨sg36460,⟨sg36459,True.intro,True.intro⟩,True.intro⟩,⟨sg36463,⟨sg36462,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36467,⟨sg36466,⟨sg36465,True.intro,True.intro⟩,True.intro⟩,⟨sg36468,True.intro,True.intro⟩⟩⟩,⟨sg36475,⟨sg36472,⟨sg36471,⟨sg36470,True.intro,True.intro⟩,True.intro⟩,⟨sg36474,⟨sg36473,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36478,⟨sg36477,⟨sg36476,True.intro,True.intro⟩,True.intro⟩,⟨sg36479,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_402All : degreeTree62_402.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36458,degreeTree62_400All,degreeTree62_401All⟩

lemma degreeTree62_403All : degreeTree62_403.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36436,degreeTree62_399All,degreeTree62_402All⟩

lemma degreeTree62_404All : degreeTree62_404.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36491,⟨sg36486,⟨sg36483,⟨sg36482,⟨sg36481,True.intro,True.intro⟩,True.intro⟩,⟨sg36485,⟨sg36484,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36489,⟨sg36488,⟨sg36487,True.intro,True.intro⟩,True.intro⟩,⟨sg36490,True.intro,True.intro⟩⟩⟩,⟨sg36497,⟨sg36494,⟨sg36493,⟨sg36492,True.intro,True.intro⟩,True.intro⟩,⟨sg36496,⟨sg36495,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36500,⟨sg36499,⟨sg36498,True.intro,True.intro⟩,True.intro⟩,⟨sg36501,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_405All : degreeTree62_405.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36513,⟨sg36508,⟨sg36505,⟨sg36504,⟨sg36503,True.intro,True.intro⟩,True.intro⟩,⟨sg36507,⟨sg36506,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36511,⟨sg36510,⟨sg36509,True.intro,True.intro⟩,True.intro⟩,⟨sg36512,True.intro,True.intro⟩⟩⟩,⟨sg36519,⟨sg36516,⟨sg36515,⟨sg36514,True.intro,True.intro⟩,True.intro⟩,⟨sg36518,⟨sg36517,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36522,⟨sg36521,⟨sg36520,True.intro,True.intro⟩,True.intro⟩,⟨sg36523,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_406All : degreeTree62_406.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36502,degreeTree62_404All,degreeTree62_405All⟩

lemma degreeTree62_407All : degreeTree62_407.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36535,⟨sg36530,⟨sg36527,⟨sg36526,⟨sg36525,True.intro,True.intro⟩,True.intro⟩,⟨sg36529,⟨sg36528,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36533,⟨sg36532,⟨sg36531,True.intro,True.intro⟩,True.intro⟩,⟨sg36534,True.intro,True.intro⟩⟩⟩,⟨sg36541,⟨sg36538,⟨sg36537,⟨sg36536,True.intro,True.intro⟩,True.intro⟩,⟨sg36540,⟨sg36539,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36544,⟨sg36543,⟨sg36542,True.intro,True.intro⟩,True.intro⟩,⟨sg36545,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_408All : degreeTree62_408.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36557,⟨sg36552,⟨sg36549,⟨sg36548,⟨sg36547,True.intro,True.intro⟩,True.intro⟩,⟨sg36551,⟨sg36550,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36555,⟨sg36554,⟨sg36553,True.intro,True.intro⟩,True.intro⟩,⟨sg36556,True.intro,True.intro⟩⟩⟩,⟨sg36562,⟨sg36560,⟨sg36559,⟨sg36558,True.intro,True.intro⟩,True.intro⟩,⟨sg36561,True.intro,True.intro⟩⟩,⟨sg36565,⟨sg36564,⟨sg36563,True.intro,True.intro⟩,True.intro⟩,⟨sg36566,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_409All : degreeTree62_409.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36546,degreeTree62_407All,degreeTree62_408All⟩

lemma degreeTree62_410All : degreeTree62_410.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36524,degreeTree62_406All,degreeTree62_409All⟩

lemma degreeTree62_411All : degreeTree62_411.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36480,degreeTree62_403All,degreeTree62_410All⟩

lemma degreeTree62_412All : degreeTree62_412.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36392,degreeTree62_396All,degreeTree62_411All⟩

lemma degreeTree62_413All : degreeTree62_413.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36578,⟨sg36573,⟨sg36570,⟨sg36569,⟨sg36568,True.intro,True.intro⟩,True.intro⟩,⟨sg36572,⟨sg36571,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36576,⟨sg36575,⟨sg36574,True.intro,True.intro⟩,True.intro⟩,⟨sg36577,True.intro,True.intro⟩⟩⟩,⟨sg36584,⟨sg36581,⟨sg36580,⟨sg36579,True.intro,True.intro⟩,True.intro⟩,⟨sg36583,⟨sg36582,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36587,⟨sg36586,⟨sg36585,True.intro,True.intro⟩,True.intro⟩,⟨sg36588,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_414All : degreeTree62_414.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36600,⟨sg36595,⟨sg36592,⟨sg36591,⟨sg36590,True.intro,True.intro⟩,True.intro⟩,⟨sg36594,⟨sg36593,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36598,⟨sg36597,⟨sg36596,True.intro,True.intro⟩,True.intro⟩,⟨sg36599,True.intro,True.intro⟩⟩⟩,⟨sg36606,⟨sg36603,⟨sg36602,⟨sg36601,True.intro,True.intro⟩,True.intro⟩,⟨sg36605,⟨sg36604,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36609,⟨sg36608,⟨sg36607,True.intro,True.intro⟩,True.intro⟩,⟨sg36610,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_415All : degreeTree62_415.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36589,degreeTree62_413All,degreeTree62_414All⟩

lemma degreeTree62_416All : degreeTree62_416.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36622,⟨sg36617,⟨sg36614,⟨sg36613,⟨sg36612,True.intro,True.intro⟩,True.intro⟩,⟨sg36616,⟨sg36615,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36620,⟨sg36619,⟨sg36618,True.intro,True.intro⟩,True.intro⟩,⟨sg36621,True.intro,True.intro⟩⟩⟩,⟨sg36628,⟨sg36625,⟨sg36624,⟨sg36623,True.intro,True.intro⟩,True.intro⟩,⟨sg36627,⟨sg36626,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36631,⟨sg36630,⟨sg36629,True.intro,True.intro⟩,True.intro⟩,⟨sg36632,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_417All : degreeTree62_417.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36644,⟨sg36639,⟨sg36636,⟨sg36635,⟨sg36634,True.intro,True.intro⟩,True.intro⟩,⟨sg36638,⟨sg36637,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36642,⟨sg36641,⟨sg36640,True.intro,True.intro⟩,True.intro⟩,⟨sg36643,True.intro,True.intro⟩⟩⟩,⟨sg36650,⟨sg36647,⟨sg36646,⟨sg36645,True.intro,True.intro⟩,True.intro⟩,⟨sg36649,⟨sg36648,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36653,⟨sg36652,⟨sg36651,True.intro,True.intro⟩,True.intro⟩,⟨sg36654,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_418All : degreeTree62_418.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36633,degreeTree62_416All,degreeTree62_417All⟩

lemma degreeTree62_419All : degreeTree62_419.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36611,degreeTree62_415All,degreeTree62_418All⟩

lemma degreeTree62_420All : degreeTree62_420.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36666,⟨sg36661,⟨sg36658,⟨sg36657,⟨sg36656,True.intro,True.intro⟩,True.intro⟩,⟨sg36660,⟨sg36659,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36664,⟨sg36663,⟨sg36662,True.intro,True.intro⟩,True.intro⟩,⟨sg36665,True.intro,True.intro⟩⟩⟩,⟨sg36672,⟨sg36669,⟨sg36668,⟨sg36667,True.intro,True.intro⟩,True.intro⟩,⟨sg36671,⟨sg36670,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36675,⟨sg36674,⟨sg36673,True.intro,True.intro⟩,True.intro⟩,⟨sg36676,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_421All : degreeTree62_421.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36688,⟨sg36683,⟨sg36680,⟨sg36679,⟨sg36678,True.intro,True.intro⟩,True.intro⟩,⟨sg36682,⟨sg36681,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36686,⟨sg36685,⟨sg36684,True.intro,True.intro⟩,True.intro⟩,⟨sg36687,True.intro,True.intro⟩⟩⟩,⟨sg36694,⟨sg36691,⟨sg36690,⟨sg36689,True.intro,True.intro⟩,True.intro⟩,⟨sg36693,⟨sg36692,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36697,⟨sg36696,⟨sg36695,True.intro,True.intro⟩,True.intro⟩,⟨sg36698,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_422All : degreeTree62_422.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36677,degreeTree62_420All,degreeTree62_421All⟩

lemma degreeTree62_423All : degreeTree62_423.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36710,⟨sg36705,⟨sg36702,⟨sg36701,⟨sg36700,True.intro,True.intro⟩,True.intro⟩,⟨sg36704,⟨sg36703,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36708,⟨sg36707,⟨sg36706,True.intro,True.intro⟩,True.intro⟩,⟨sg36709,True.intro,True.intro⟩⟩⟩,⟨sg36716,⟨sg36713,⟨sg36712,⟨sg36711,True.intro,True.intro⟩,True.intro⟩,⟨sg36715,⟨sg36714,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36719,⟨sg36718,⟨sg36717,True.intro,True.intro⟩,True.intro⟩,⟨sg36720,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_424All : degreeTree62_424.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36732,⟨sg36727,⟨sg36724,⟨sg36723,⟨sg36722,True.intro,True.intro⟩,True.intro⟩,⟨sg36726,⟨sg36725,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36730,⟨sg36729,⟨sg36728,True.intro,True.intro⟩,True.intro⟩,⟨sg36731,True.intro,True.intro⟩⟩⟩,⟨sg36738,⟨sg36735,⟨sg36734,⟨sg36733,True.intro,True.intro⟩,True.intro⟩,⟨sg36737,⟨sg36736,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36741,⟨sg36740,⟨sg36739,True.intro,True.intro⟩,True.intro⟩,⟨sg36742,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_425All : degreeTree62_425.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36721,degreeTree62_423All,degreeTree62_424All⟩

lemma degreeTree62_426All : degreeTree62_426.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36699,degreeTree62_422All,degreeTree62_425All⟩

lemma degreeTree62_427All : degreeTree62_427.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36655,degreeTree62_419All,degreeTree62_426All⟩

lemma degreeTree62_428All : degreeTree62_428.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36754,⟨sg36749,⟨sg36746,⟨sg36745,⟨sg36744,True.intro,True.intro⟩,True.intro⟩,⟨sg36748,⟨sg36747,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36752,⟨sg36751,⟨sg36750,True.intro,True.intro⟩,True.intro⟩,⟨sg36753,True.intro,True.intro⟩⟩⟩,⟨sg36760,⟨sg36757,⟨sg36756,⟨sg36755,True.intro,True.intro⟩,True.intro⟩,⟨sg36759,⟨sg36758,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36763,⟨sg36762,⟨sg36761,True.intro,True.intro⟩,True.intro⟩,⟨sg36764,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_429All : degreeTree62_429.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36776,⟨sg36771,⟨sg36768,⟨sg36767,⟨sg36766,True.intro,True.intro⟩,True.intro⟩,⟨sg36770,⟨sg36769,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36774,⟨sg36773,⟨sg36772,True.intro,True.intro⟩,True.intro⟩,⟨sg36775,True.intro,True.intro⟩⟩⟩,⟨sg36782,⟨sg36779,⟨sg36778,⟨sg36777,True.intro,True.intro⟩,True.intro⟩,⟨sg36781,⟨sg36780,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36785,⟨sg36784,⟨sg36783,True.intro,True.intro⟩,True.intro⟩,⟨sg36786,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_430All : degreeTree62_430.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36765,degreeTree62_428All,degreeTree62_429All⟩

lemma degreeTree62_431All : degreeTree62_431.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36798,⟨sg36793,⟨sg36790,⟨sg36789,⟨sg36788,True.intro,True.intro⟩,True.intro⟩,⟨sg36792,⟨sg36791,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36796,⟨sg36795,⟨sg36794,True.intro,True.intro⟩,True.intro⟩,⟨sg36797,True.intro,True.intro⟩⟩⟩,⟨sg36804,⟨sg36801,⟨sg36800,⟨sg36799,True.intro,True.intro⟩,True.intro⟩,⟨sg36803,⟨sg36802,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36807,⟨sg36806,⟨sg36805,True.intro,True.intro⟩,True.intro⟩,⟨sg36808,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_432All : degreeTree62_432.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36820,⟨sg36815,⟨sg36812,⟨sg36811,⟨sg36810,True.intro,True.intro⟩,True.intro⟩,⟨sg36814,⟨sg36813,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36818,⟨sg36817,⟨sg36816,True.intro,True.intro⟩,True.intro⟩,⟨sg36819,True.intro,True.intro⟩⟩⟩,⟨sg36826,⟨sg36823,⟨sg36822,⟨sg36821,True.intro,True.intro⟩,True.intro⟩,⟨sg36825,⟨sg36824,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36829,⟨sg36828,⟨sg36827,True.intro,True.intro⟩,True.intro⟩,⟨sg36830,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_433All : degreeTree62_433.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36809,degreeTree62_431All,degreeTree62_432All⟩

lemma degreeTree62_434All : degreeTree62_434.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36787,degreeTree62_430All,degreeTree62_433All⟩

lemma degreeTree62_435All : degreeTree62_435.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36842,⟨sg36837,⟨sg36834,⟨sg36833,⟨sg36832,True.intro,True.intro⟩,True.intro⟩,⟨sg36836,⟨sg36835,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36840,⟨sg36839,⟨sg36838,True.intro,True.intro⟩,True.intro⟩,⟨sg36841,True.intro,True.intro⟩⟩⟩,⟨sg36848,⟨sg36845,⟨sg36844,⟨sg36843,True.intro,True.intro⟩,True.intro⟩,⟨sg36847,⟨sg36846,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36851,⟨sg36850,⟨sg36849,True.intro,True.intro⟩,True.intro⟩,⟨sg36852,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_436All : degreeTree62_436.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36864,⟨sg36859,⟨sg36856,⟨sg36855,⟨sg36854,True.intro,True.intro⟩,True.intro⟩,⟨sg36858,⟨sg36857,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36862,⟨sg36861,⟨sg36860,True.intro,True.intro⟩,True.intro⟩,⟨sg36863,True.intro,True.intro⟩⟩⟩,⟨sg36870,⟨sg36867,⟨sg36866,⟨sg36865,True.intro,True.intro⟩,True.intro⟩,⟨sg36869,⟨sg36868,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36873,⟨sg36872,⟨sg36871,True.intro,True.intro⟩,True.intro⟩,⟨sg36874,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_437All : degreeTree62_437.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36853,degreeTree62_435All,degreeTree62_436All⟩

lemma degreeTree62_438All : degreeTree62_438.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36886,⟨sg36881,⟨sg36878,⟨sg36877,⟨sg36876,True.intro,True.intro⟩,True.intro⟩,⟨sg36880,⟨sg36879,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36884,⟨sg36883,⟨sg36882,True.intro,True.intro⟩,True.intro⟩,⟨sg36885,True.intro,True.intro⟩⟩⟩,⟨sg36892,⟨sg36889,⟨sg36888,⟨sg36887,True.intro,True.intro⟩,True.intro⟩,⟨sg36891,⟨sg36890,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36895,⟨sg36894,⟨sg36893,True.intro,True.intro⟩,True.intro⟩,⟨sg36896,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_439All : degreeTree62_439.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36908,⟨sg36903,⟨sg36900,⟨sg36899,⟨sg36898,True.intro,True.intro⟩,True.intro⟩,⟨sg36902,⟨sg36901,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36906,⟨sg36905,⟨sg36904,True.intro,True.intro⟩,True.intro⟩,⟨sg36907,True.intro,True.intro⟩⟩⟩,⟨sg36913,⟨sg36911,⟨sg36910,⟨sg36909,True.intro,True.intro⟩,True.intro⟩,⟨sg36912,True.intro,True.intro⟩⟩,⟨sg36916,⟨sg36915,⟨sg36914,True.intro,True.intro⟩,True.intro⟩,⟨sg36917,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_440All : degreeTree62_440.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36897,degreeTree62_438All,degreeTree62_439All⟩

lemma degreeTree62_441All : degreeTree62_441.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36875,degreeTree62_437All,degreeTree62_440All⟩

lemma degreeTree62_442All : degreeTree62_442.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36831,degreeTree62_434All,degreeTree62_441All⟩

lemma degreeTree62_443All : degreeTree62_443.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36743,degreeTree62_427All,degreeTree62_442All⟩

lemma degreeTree62_444All : degreeTree62_444.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36567,degreeTree62_412All,degreeTree62_443All⟩

lemma degreeTree62_445All : degreeTree62_445.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36929,⟨sg36924,⟨sg36921,⟨sg36920,⟨sg36919,True.intro,True.intro⟩,True.intro⟩,⟨sg36923,⟨sg36922,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36927,⟨sg36926,⟨sg36925,True.intro,True.intro⟩,True.intro⟩,⟨sg36928,True.intro,True.intro⟩⟩⟩,⟨sg36935,⟨sg36932,⟨sg36931,⟨sg36930,True.intro,True.intro⟩,True.intro⟩,⟨sg36934,⟨sg36933,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36938,⟨sg36937,⟨sg36936,True.intro,True.intro⟩,True.intro⟩,⟨sg36939,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_446All : degreeTree62_446.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36951,⟨sg36946,⟨sg36943,⟨sg36942,⟨sg36941,True.intro,True.intro⟩,True.intro⟩,⟨sg36945,⟨sg36944,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36949,⟨sg36948,⟨sg36947,True.intro,True.intro⟩,True.intro⟩,⟨sg36950,True.intro,True.intro⟩⟩⟩,⟨sg36957,⟨sg36954,⟨sg36953,⟨sg36952,True.intro,True.intro⟩,True.intro⟩,⟨sg36956,⟨sg36955,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36960,⟨sg36959,⟨sg36958,True.intro,True.intro⟩,True.intro⟩,⟨sg36961,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_447All : degreeTree62_447.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36940,degreeTree62_445All,degreeTree62_446All⟩

lemma degreeTree62_448All : degreeTree62_448.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36973,⟨sg36968,⟨sg36965,⟨sg36964,⟨sg36963,True.intro,True.intro⟩,True.intro⟩,⟨sg36967,⟨sg36966,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36971,⟨sg36970,⟨sg36969,True.intro,True.intro⟩,True.intro⟩,⟨sg36972,True.intro,True.intro⟩⟩⟩,⟨sg36979,⟨sg36976,⟨sg36975,⟨sg36974,True.intro,True.intro⟩,True.intro⟩,⟨sg36978,⟨sg36977,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36982,⟨sg36981,⟨sg36980,True.intro,True.intro⟩,True.intro⟩,⟨sg36983,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_449All : degreeTree62_449.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36995,⟨sg36990,⟨sg36987,⟨sg36986,⟨sg36985,True.intro,True.intro⟩,True.intro⟩,⟨sg36989,⟨sg36988,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg36993,⟨sg36992,⟨sg36991,True.intro,True.intro⟩,True.intro⟩,⟨sg36994,True.intro,True.intro⟩⟩⟩,⟨sg37001,⟨sg36998,⟨sg36997,⟨sg36996,True.intro,True.intro⟩,True.intro⟩,⟨sg37000,⟨sg36999,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37004,⟨sg37003,⟨sg37002,True.intro,True.intro⟩,True.intro⟩,⟨sg37005,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_450All : degreeTree62_450.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36984,degreeTree62_448All,degreeTree62_449All⟩

lemma degreeTree62_451All : degreeTree62_451.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36962,degreeTree62_447All,degreeTree62_450All⟩

lemma degreeTree62_452All : degreeTree62_452.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37017,⟨sg37012,⟨sg37009,⟨sg37008,⟨sg37007,True.intro,True.intro⟩,True.intro⟩,⟨sg37011,⟨sg37010,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37015,⟨sg37014,⟨sg37013,True.intro,True.intro⟩,True.intro⟩,⟨sg37016,True.intro,True.intro⟩⟩⟩,⟨sg37023,⟨sg37020,⟨sg37019,⟨sg37018,True.intro,True.intro⟩,True.intro⟩,⟨sg37022,⟨sg37021,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37026,⟨sg37025,⟨sg37024,True.intro,True.intro⟩,True.intro⟩,⟨sg37027,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_453All : degreeTree62_453.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37039,⟨sg37034,⟨sg37031,⟨sg37030,⟨sg37029,True.intro,True.intro⟩,True.intro⟩,⟨sg37033,⟨sg37032,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37037,⟨sg37036,⟨sg37035,True.intro,True.intro⟩,True.intro⟩,⟨sg37038,True.intro,True.intro⟩⟩⟩,⟨sg37045,⟨sg37042,⟨sg37041,⟨sg37040,True.intro,True.intro⟩,True.intro⟩,⟨sg37044,⟨sg37043,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37048,⟨sg37047,⟨sg37046,True.intro,True.intro⟩,True.intro⟩,⟨sg37049,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_454All : degreeTree62_454.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37028,degreeTree62_452All,degreeTree62_453All⟩

lemma degreeTree62_455All : degreeTree62_455.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37061,⟨sg37056,⟨sg37053,⟨sg37052,⟨sg37051,True.intro,True.intro⟩,True.intro⟩,⟨sg37055,⟨sg37054,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37059,⟨sg37058,⟨sg37057,True.intro,True.intro⟩,True.intro⟩,⟨sg37060,True.intro,True.intro⟩⟩⟩,⟨sg37067,⟨sg37064,⟨sg37063,⟨sg37062,True.intro,True.intro⟩,True.intro⟩,⟨sg37066,⟨sg37065,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37070,⟨sg37069,⟨sg37068,True.intro,True.intro⟩,True.intro⟩,⟨sg37071,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_456All : degreeTree62_456.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37083,⟨sg37078,⟨sg37075,⟨sg37074,⟨sg37073,True.intro,True.intro⟩,True.intro⟩,⟨sg37077,⟨sg37076,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37081,⟨sg37080,⟨sg37079,True.intro,True.intro⟩,True.intro⟩,⟨sg37082,True.intro,True.intro⟩⟩⟩,⟨sg37089,⟨sg37086,⟨sg37085,⟨sg37084,True.intro,True.intro⟩,True.intro⟩,⟨sg37088,⟨sg37087,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37092,⟨sg37091,⟨sg37090,True.intro,True.intro⟩,True.intro⟩,⟨sg37093,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_457All : degreeTree62_457.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37072,degreeTree62_455All,degreeTree62_456All⟩

lemma degreeTree62_458All : degreeTree62_458.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37050,degreeTree62_454All,degreeTree62_457All⟩

lemma degreeTree62_459All : degreeTree62_459.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37006,degreeTree62_451All,degreeTree62_458All⟩

lemma degreeTree62_460All : degreeTree62_460.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37105,⟨sg37100,⟨sg37097,⟨sg37096,⟨sg37095,True.intro,True.intro⟩,True.intro⟩,⟨sg37099,⟨sg37098,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37103,⟨sg37102,⟨sg37101,True.intro,True.intro⟩,True.intro⟩,⟨sg37104,True.intro,True.intro⟩⟩⟩,⟨sg37111,⟨sg37108,⟨sg37107,⟨sg37106,True.intro,True.intro⟩,True.intro⟩,⟨sg37110,⟨sg37109,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37114,⟨sg37113,⟨sg37112,True.intro,True.intro⟩,True.intro⟩,⟨sg37115,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_461All : degreeTree62_461.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37127,⟨sg37122,⟨sg37119,⟨sg37118,⟨sg37117,True.intro,True.intro⟩,True.intro⟩,⟨sg37121,⟨sg37120,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37125,⟨sg37124,⟨sg37123,True.intro,True.intro⟩,True.intro⟩,⟨sg37126,True.intro,True.intro⟩⟩⟩,⟨sg37133,⟨sg37130,⟨sg37129,⟨sg37128,True.intro,True.intro⟩,True.intro⟩,⟨sg37132,⟨sg37131,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37136,⟨sg37135,⟨sg37134,True.intro,True.intro⟩,True.intro⟩,⟨sg37137,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_462All : degreeTree62_462.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37116,degreeTree62_460All,degreeTree62_461All⟩

lemma degreeTree62_463All : degreeTree62_463.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37149,⟨sg37144,⟨sg37141,⟨sg37140,⟨sg37139,True.intro,True.intro⟩,True.intro⟩,⟨sg37143,⟨sg37142,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37147,⟨sg37146,⟨sg37145,True.intro,True.intro⟩,True.intro⟩,⟨sg37148,True.intro,True.intro⟩⟩⟩,⟨sg37155,⟨sg37152,⟨sg37151,⟨sg37150,True.intro,True.intro⟩,True.intro⟩,⟨sg37154,⟨sg37153,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37158,⟨sg37157,⟨sg37156,True.intro,True.intro⟩,True.intro⟩,⟨sg37159,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_464All : degreeTree62_464.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37171,⟨sg37166,⟨sg37163,⟨sg37162,⟨sg37161,True.intro,True.intro⟩,True.intro⟩,⟨sg37165,⟨sg37164,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37169,⟨sg37168,⟨sg37167,True.intro,True.intro⟩,True.intro⟩,⟨sg37170,True.intro,True.intro⟩⟩⟩,⟨sg37177,⟨sg37174,⟨sg37173,⟨sg37172,True.intro,True.intro⟩,True.intro⟩,⟨sg37176,⟨sg37175,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37180,⟨sg37179,⟨sg37178,True.intro,True.intro⟩,True.intro⟩,⟨sg37181,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_465All : degreeTree62_465.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37160,degreeTree62_463All,degreeTree62_464All⟩

lemma degreeTree62_466All : degreeTree62_466.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37138,degreeTree62_462All,degreeTree62_465All⟩

lemma degreeTree62_467All : degreeTree62_467.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37193,⟨sg37188,⟨sg37185,⟨sg37184,⟨sg37183,True.intro,True.intro⟩,True.intro⟩,⟨sg37187,⟨sg37186,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37191,⟨sg37190,⟨sg37189,True.intro,True.intro⟩,True.intro⟩,⟨sg37192,True.intro,True.intro⟩⟩⟩,⟨sg37199,⟨sg37196,⟨sg37195,⟨sg37194,True.intro,True.intro⟩,True.intro⟩,⟨sg37198,⟨sg37197,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37202,⟨sg37201,⟨sg37200,True.intro,True.intro⟩,True.intro⟩,⟨sg37203,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_468All : degreeTree62_468.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37215,⟨sg37210,⟨sg37207,⟨sg37206,⟨sg37205,True.intro,True.intro⟩,True.intro⟩,⟨sg37209,⟨sg37208,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37213,⟨sg37212,⟨sg37211,True.intro,True.intro⟩,True.intro⟩,⟨sg37214,True.intro,True.intro⟩⟩⟩,⟨sg37221,⟨sg37218,⟨sg37217,⟨sg37216,True.intro,True.intro⟩,True.intro⟩,⟨sg37220,⟨sg37219,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37224,⟨sg37223,⟨sg37222,True.intro,True.intro⟩,True.intro⟩,⟨sg37225,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_469All : degreeTree62_469.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37204,degreeTree62_467All,degreeTree62_468All⟩

lemma degreeTree62_470All : degreeTree62_470.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37237,⟨sg37232,⟨sg37229,⟨sg37228,⟨sg37227,True.intro,True.intro⟩,True.intro⟩,⟨sg37231,⟨sg37230,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37235,⟨sg37234,⟨sg37233,True.intro,True.intro⟩,True.intro⟩,⟨sg37236,True.intro,True.intro⟩⟩⟩,⟨sg37243,⟨sg37240,⟨sg37239,⟨sg37238,True.intro,True.intro⟩,True.intro⟩,⟨sg37242,⟨sg37241,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37246,⟨sg37245,⟨sg37244,True.intro,True.intro⟩,True.intro⟩,⟨sg37247,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_471All : degreeTree62_471.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37259,⟨sg37254,⟨sg37251,⟨sg37250,⟨sg37249,True.intro,True.intro⟩,True.intro⟩,⟨sg37253,⟨sg37252,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37257,⟨sg37256,⟨sg37255,True.intro,True.intro⟩,True.intro⟩,⟨sg37258,True.intro,True.intro⟩⟩⟩,⟨sg37264,⟨sg37262,⟨sg37261,⟨sg37260,True.intro,True.intro⟩,True.intro⟩,⟨sg37263,True.intro,True.intro⟩⟩,⟨sg37267,⟨sg37266,⟨sg37265,True.intro,True.intro⟩,True.intro⟩,⟨sg37268,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_472All : degreeTree62_472.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37248,degreeTree62_470All,degreeTree62_471All⟩

lemma degreeTree62_473All : degreeTree62_473.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37226,degreeTree62_469All,degreeTree62_472All⟩

lemma degreeTree62_474All : degreeTree62_474.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37182,degreeTree62_466All,degreeTree62_473All⟩

lemma degreeTree62_475All : degreeTree62_475.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37094,degreeTree62_459All,degreeTree62_474All⟩

lemma degreeTree62_476All : degreeTree62_476.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37280,⟨sg37275,⟨sg37272,⟨sg37271,⟨sg37270,True.intro,True.intro⟩,True.intro⟩,⟨sg37274,⟨sg37273,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37278,⟨sg37277,⟨sg37276,True.intro,True.intro⟩,True.intro⟩,⟨sg37279,True.intro,True.intro⟩⟩⟩,⟨sg37286,⟨sg37283,⟨sg37282,⟨sg37281,True.intro,True.intro⟩,True.intro⟩,⟨sg37285,⟨sg37284,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37289,⟨sg37288,⟨sg37287,True.intro,True.intro⟩,True.intro⟩,⟨sg37290,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_477All : degreeTree62_477.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37302,⟨sg37297,⟨sg37294,⟨sg37293,⟨sg37292,True.intro,True.intro⟩,True.intro⟩,⟨sg37296,⟨sg37295,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37300,⟨sg37299,⟨sg37298,True.intro,True.intro⟩,True.intro⟩,⟨sg37301,True.intro,True.intro⟩⟩⟩,⟨sg37308,⟨sg37305,⟨sg37304,⟨sg37303,True.intro,True.intro⟩,True.intro⟩,⟨sg37307,⟨sg37306,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37311,⟨sg37310,⟨sg37309,True.intro,True.intro⟩,True.intro⟩,⟨sg37312,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_478All : degreeTree62_478.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37291,degreeTree62_476All,degreeTree62_477All⟩

lemma degreeTree62_479All : degreeTree62_479.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37324,⟨sg37319,⟨sg37316,⟨sg37315,⟨sg37314,True.intro,True.intro⟩,True.intro⟩,⟨sg37318,⟨sg37317,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37322,⟨sg37321,⟨sg37320,True.intro,True.intro⟩,True.intro⟩,⟨sg37323,True.intro,True.intro⟩⟩⟩,⟨sg37330,⟨sg37327,⟨sg37326,⟨sg37325,True.intro,True.intro⟩,True.intro⟩,⟨sg37329,⟨sg37328,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37333,⟨sg37332,⟨sg37331,True.intro,True.intro⟩,True.intro⟩,⟨sg37334,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_480All : degreeTree62_480.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37346,⟨sg37341,⟨sg37338,⟨sg37337,⟨sg37336,True.intro,True.intro⟩,True.intro⟩,⟨sg37340,⟨sg37339,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37344,⟨sg37343,⟨sg37342,True.intro,True.intro⟩,True.intro⟩,⟨sg37345,True.intro,True.intro⟩⟩⟩,⟨sg37352,⟨sg37349,⟨sg37348,⟨sg37347,True.intro,True.intro⟩,True.intro⟩,⟨sg37351,⟨sg37350,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37355,⟨sg37354,⟨sg37353,True.intro,True.intro⟩,True.intro⟩,⟨sg37356,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_481All : degreeTree62_481.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37335,degreeTree62_479All,degreeTree62_480All⟩

lemma degreeTree62_482All : degreeTree62_482.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37313,degreeTree62_478All,degreeTree62_481All⟩

lemma degreeTree62_483All : degreeTree62_483.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37368,⟨sg37363,⟨sg37360,⟨sg37359,⟨sg37358,True.intro,True.intro⟩,True.intro⟩,⟨sg37362,⟨sg37361,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37366,⟨sg37365,⟨sg37364,True.intro,True.intro⟩,True.intro⟩,⟨sg37367,True.intro,True.intro⟩⟩⟩,⟨sg37374,⟨sg37371,⟨sg37370,⟨sg37369,True.intro,True.intro⟩,True.intro⟩,⟨sg37373,⟨sg37372,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37377,⟨sg37376,⟨sg37375,True.intro,True.intro⟩,True.intro⟩,⟨sg37378,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_484All : degreeTree62_484.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37390,⟨sg37385,⟨sg37382,⟨sg37381,⟨sg37380,True.intro,True.intro⟩,True.intro⟩,⟨sg37384,⟨sg37383,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37388,⟨sg37387,⟨sg37386,True.intro,True.intro⟩,True.intro⟩,⟨sg37389,True.intro,True.intro⟩⟩⟩,⟨sg37396,⟨sg37393,⟨sg37392,⟨sg37391,True.intro,True.intro⟩,True.intro⟩,⟨sg37395,⟨sg37394,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37399,⟨sg37398,⟨sg37397,True.intro,True.intro⟩,True.intro⟩,⟨sg37400,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_485All : degreeTree62_485.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37379,degreeTree62_483All,degreeTree62_484All⟩

lemma degreeTree62_486All : degreeTree62_486.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37412,⟨sg37407,⟨sg37404,⟨sg37403,⟨sg37402,True.intro,True.intro⟩,True.intro⟩,⟨sg37406,⟨sg37405,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37410,⟨sg37409,⟨sg37408,True.intro,True.intro⟩,True.intro⟩,⟨sg37411,True.intro,True.intro⟩⟩⟩,⟨sg37418,⟨sg37415,⟨sg37414,⟨sg37413,True.intro,True.intro⟩,True.intro⟩,⟨sg37417,⟨sg37416,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37421,⟨sg37420,⟨sg37419,True.intro,True.intro⟩,True.intro⟩,⟨sg37422,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_487All : degreeTree62_487.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37434,⟨sg37429,⟨sg37426,⟨sg37425,⟨sg37424,True.intro,True.intro⟩,True.intro⟩,⟨sg37428,⟨sg37427,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37432,⟨sg37431,⟨sg37430,True.intro,True.intro⟩,True.intro⟩,⟨sg37433,True.intro,True.intro⟩⟩⟩,⟨sg37439,⟨sg37437,⟨sg37436,⟨sg37435,True.intro,True.intro⟩,True.intro⟩,⟨sg37438,True.intro,True.intro⟩⟩,⟨sg37442,⟨sg37441,⟨sg37440,True.intro,True.intro⟩,True.intro⟩,⟨sg37443,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_488All : degreeTree62_488.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37423,degreeTree62_486All,degreeTree62_487All⟩

lemma degreeTree62_489All : degreeTree62_489.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37401,degreeTree62_485All,degreeTree62_488All⟩

lemma degreeTree62_490All : degreeTree62_490.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37357,degreeTree62_482All,degreeTree62_489All⟩

lemma degreeTree62_491All : degreeTree62_491.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37455,⟨sg37450,⟨sg37447,⟨sg37446,⟨sg37445,True.intro,True.intro⟩,True.intro⟩,⟨sg37449,⟨sg37448,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37453,⟨sg37452,⟨sg37451,True.intro,True.intro⟩,True.intro⟩,⟨sg37454,True.intro,True.intro⟩⟩⟩,⟨sg37461,⟨sg37458,⟨sg37457,⟨sg37456,True.intro,True.intro⟩,True.intro⟩,⟨sg37460,⟨sg37459,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37464,⟨sg37463,⟨sg37462,True.intro,True.intro⟩,True.intro⟩,⟨sg37465,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_492All : degreeTree62_492.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37477,⟨sg37472,⟨sg37469,⟨sg37468,⟨sg37467,True.intro,True.intro⟩,True.intro⟩,⟨sg37471,⟨sg37470,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37475,⟨sg37474,⟨sg37473,True.intro,True.intro⟩,True.intro⟩,⟨sg37476,True.intro,True.intro⟩⟩⟩,⟨sg37483,⟨sg37480,⟨sg37479,⟨sg37478,True.intro,True.intro⟩,True.intro⟩,⟨sg37482,⟨sg37481,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37486,⟨sg37485,⟨sg37484,True.intro,True.intro⟩,True.intro⟩,⟨sg37487,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_493All : degreeTree62_493.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37466,degreeTree62_491All,degreeTree62_492All⟩

lemma degreeTree62_494All : degreeTree62_494.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37499,⟨sg37494,⟨sg37491,⟨sg37490,⟨sg37489,True.intro,True.intro⟩,True.intro⟩,⟨sg37493,⟨sg37492,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37497,⟨sg37496,⟨sg37495,True.intro,True.intro⟩,True.intro⟩,⟨sg37498,True.intro,True.intro⟩⟩⟩,⟨sg37505,⟨sg37502,⟨sg37501,⟨sg37500,True.intro,True.intro⟩,True.intro⟩,⟨sg37504,⟨sg37503,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37508,⟨sg37507,⟨sg37506,True.intro,True.intro⟩,True.intro⟩,⟨sg37509,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_495All : degreeTree62_495.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37521,⟨sg37516,⟨sg37513,⟨sg37512,⟨sg37511,True.intro,True.intro⟩,True.intro⟩,⟨sg37515,⟨sg37514,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37519,⟨sg37518,⟨sg37517,True.intro,True.intro⟩,True.intro⟩,⟨sg37520,True.intro,True.intro⟩⟩⟩,⟨sg37527,⟨sg37524,⟨sg37523,⟨sg37522,True.intro,True.intro⟩,True.intro⟩,⟨sg37526,⟨sg37525,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37530,⟨sg37529,⟨sg37528,True.intro,True.intro⟩,True.intro⟩,⟨sg37531,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_496All : degreeTree62_496.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37510,degreeTree62_494All,degreeTree62_495All⟩

lemma degreeTree62_497All : degreeTree62_497.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37488,degreeTree62_493All,degreeTree62_496All⟩

lemma degreeTree62_498All : degreeTree62_498.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37543,⟨sg37538,⟨sg37535,⟨sg37534,⟨sg37533,True.intro,True.intro⟩,True.intro⟩,⟨sg37537,⟨sg37536,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37541,⟨sg37540,⟨sg37539,True.intro,True.intro⟩,True.intro⟩,⟨sg37542,True.intro,True.intro⟩⟩⟩,⟨sg37549,⟨sg37546,⟨sg37545,⟨sg37544,True.intro,True.intro⟩,True.intro⟩,⟨sg37548,⟨sg37547,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37552,⟨sg37551,⟨sg37550,True.intro,True.intro⟩,True.intro⟩,⟨sg37553,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_499All : degreeTree62_499.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37565,⟨sg37560,⟨sg37557,⟨sg37556,⟨sg37555,True.intro,True.intro⟩,True.intro⟩,⟨sg37559,⟨sg37558,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37563,⟨sg37562,⟨sg37561,True.intro,True.intro⟩,True.intro⟩,⟨sg37564,True.intro,True.intro⟩⟩⟩,⟨sg37571,⟨sg37568,⟨sg37567,⟨sg37566,True.intro,True.intro⟩,True.intro⟩,⟨sg37570,⟨sg37569,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37574,⟨sg37573,⟨sg37572,True.intro,True.intro⟩,True.intro⟩,⟨sg37575,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_500All : degreeTree62_500.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37554,degreeTree62_498All,degreeTree62_499All⟩

lemma degreeTree62_501All : degreeTree62_501.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37587,⟨sg37582,⟨sg37579,⟨sg37578,⟨sg37577,True.intro,True.intro⟩,True.intro⟩,⟨sg37581,⟨sg37580,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37585,⟨sg37584,⟨sg37583,True.intro,True.intro⟩,True.intro⟩,⟨sg37586,True.intro,True.intro⟩⟩⟩,⟨sg37593,⟨sg37590,⟨sg37589,⟨sg37588,True.intro,True.intro⟩,True.intro⟩,⟨sg37592,⟨sg37591,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37596,⟨sg37595,⟨sg37594,True.intro,True.intro⟩,True.intro⟩,⟨sg37597,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_502All : degreeTree62_502.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37609,⟨sg37604,⟨sg37601,⟨sg37600,⟨sg37599,True.intro,True.intro⟩,True.intro⟩,⟨sg37603,⟨sg37602,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37607,⟨sg37606,⟨sg37605,True.intro,True.intro⟩,True.intro⟩,⟨sg37608,True.intro,True.intro⟩⟩⟩,⟨sg37614,⟨sg37612,⟨sg37611,⟨sg37610,True.intro,True.intro⟩,True.intro⟩,⟨sg37613,True.intro,True.intro⟩⟩,⟨sg37617,⟨sg37616,⟨sg37615,True.intro,True.intro⟩,True.intro⟩,⟨sg37618,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_503All : degreeTree62_503.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37598,degreeTree62_501All,degreeTree62_502All⟩

lemma degreeTree62_504All : degreeTree62_504.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37576,degreeTree62_500All,degreeTree62_503All⟩

lemma degreeTree62_505All : degreeTree62_505.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37532,degreeTree62_497All,degreeTree62_504All⟩

lemma degreeTree62_506All : degreeTree62_506.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37444,degreeTree62_490All,degreeTree62_505All⟩

lemma degreeTree62_507All : degreeTree62_507.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37269,degreeTree62_475All,degreeTree62_506All⟩

lemma degreeTree62_508All : degreeTree62_508.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36918,degreeTree62_444All,degreeTree62_507All⟩

lemma degreeTree62_509All : degreeTree62_509.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg36216,degreeTree62_381All,degreeTree62_508All⟩

lemma degreeTree62_510All : degreeTree62_510.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg34812,degreeTree62_254All,degreeTree62_509All⟩

lemma degreeTree62_511All : degreeTree62_511.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37630,⟨sg37625,⟨sg37622,⟨sg37621,⟨sg37620,True.intro,True.intro⟩,True.intro⟩,⟨sg37624,⟨sg37623,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37628,⟨sg37627,⟨sg37626,True.intro,True.intro⟩,True.intro⟩,⟨sg37629,True.intro,True.intro⟩⟩⟩,⟨sg37636,⟨sg37633,⟨sg37632,⟨sg37631,True.intro,True.intro⟩,True.intro⟩,⟨sg37635,⟨sg37634,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37639,⟨sg37638,⟨sg37637,True.intro,True.intro⟩,True.intro⟩,⟨sg37640,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_512All : degreeTree62_512.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37652,⟨sg37647,⟨sg37644,⟨sg37643,⟨sg37642,True.intro,True.intro⟩,True.intro⟩,⟨sg37646,⟨sg37645,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37650,⟨sg37649,⟨sg37648,True.intro,True.intro⟩,True.intro⟩,⟨sg37651,True.intro,True.intro⟩⟩⟩,⟨sg37658,⟨sg37655,⟨sg37654,⟨sg37653,True.intro,True.intro⟩,True.intro⟩,⟨sg37657,⟨sg37656,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37661,⟨sg37660,⟨sg37659,True.intro,True.intro⟩,True.intro⟩,⟨sg37662,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_513All : degreeTree62_513.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37641,degreeTree62_511All,degreeTree62_512All⟩

lemma degreeTree62_514All : degreeTree62_514.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37674,⟨sg37669,⟨sg37666,⟨sg37665,⟨sg37664,True.intro,True.intro⟩,True.intro⟩,⟨sg37668,⟨sg37667,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37672,⟨sg37671,⟨sg37670,True.intro,True.intro⟩,True.intro⟩,⟨sg37673,True.intro,True.intro⟩⟩⟩,⟨sg37680,⟨sg37677,⟨sg37676,⟨sg37675,True.intro,True.intro⟩,True.intro⟩,⟨sg37679,⟨sg37678,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37683,⟨sg37682,⟨sg37681,True.intro,True.intro⟩,True.intro⟩,⟨sg37684,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_515All : degreeTree62_515.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37696,⟨sg37691,⟨sg37688,⟨sg37687,⟨sg37686,True.intro,True.intro⟩,True.intro⟩,⟨sg37690,⟨sg37689,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37694,⟨sg37693,⟨sg37692,True.intro,True.intro⟩,True.intro⟩,⟨sg37695,True.intro,True.intro⟩⟩⟩,⟨sg37702,⟨sg37699,⟨sg37698,⟨sg37697,True.intro,True.intro⟩,True.intro⟩,⟨sg37701,⟨sg37700,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37705,⟨sg37704,⟨sg37703,True.intro,True.intro⟩,True.intro⟩,⟨sg37706,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_516All : degreeTree62_516.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37685,degreeTree62_514All,degreeTree62_515All⟩

lemma degreeTree62_517All : degreeTree62_517.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37663,degreeTree62_513All,degreeTree62_516All⟩

lemma degreeTree62_518All : degreeTree62_518.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37718,⟨sg37713,⟨sg37710,⟨sg37709,⟨sg37708,True.intro,True.intro⟩,True.intro⟩,⟨sg37712,⟨sg37711,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37716,⟨sg37715,⟨sg37714,True.intro,True.intro⟩,True.intro⟩,⟨sg37717,True.intro,True.intro⟩⟩⟩,⟨sg37724,⟨sg37721,⟨sg37720,⟨sg37719,True.intro,True.intro⟩,True.intro⟩,⟨sg37723,⟨sg37722,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37727,⟨sg37726,⟨sg37725,True.intro,True.intro⟩,True.intro⟩,⟨sg37728,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_519All : degreeTree62_519.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37740,⟨sg37735,⟨sg37732,⟨sg37731,⟨sg37730,True.intro,True.intro⟩,True.intro⟩,⟨sg37734,⟨sg37733,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37738,⟨sg37737,⟨sg37736,True.intro,True.intro⟩,True.intro⟩,⟨sg37739,True.intro,True.intro⟩⟩⟩,⟨sg37746,⟨sg37743,⟨sg37742,⟨sg37741,True.intro,True.intro⟩,True.intro⟩,⟨sg37745,⟨sg37744,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37749,⟨sg37748,⟨sg37747,True.intro,True.intro⟩,True.intro⟩,⟨sg37750,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_520All : degreeTree62_520.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37729,degreeTree62_518All,degreeTree62_519All⟩

lemma degreeTree62_521All : degreeTree62_521.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37762,⟨sg37757,⟨sg37754,⟨sg37753,⟨sg37752,True.intro,True.intro⟩,True.intro⟩,⟨sg37756,⟨sg37755,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37760,⟨sg37759,⟨sg37758,True.intro,True.intro⟩,True.intro⟩,⟨sg37761,True.intro,True.intro⟩⟩⟩,⟨sg37768,⟨sg37765,⟨sg37764,⟨sg37763,True.intro,True.intro⟩,True.intro⟩,⟨sg37767,⟨sg37766,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37771,⟨sg37770,⟨sg37769,True.intro,True.intro⟩,True.intro⟩,⟨sg37772,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_522All : degreeTree62_522.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37784,⟨sg37779,⟨sg37776,⟨sg37775,⟨sg37774,True.intro,True.intro⟩,True.intro⟩,⟨sg37778,⟨sg37777,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37782,⟨sg37781,⟨sg37780,True.intro,True.intro⟩,True.intro⟩,⟨sg37783,True.intro,True.intro⟩⟩⟩,⟨sg37790,⟨sg37787,⟨sg37786,⟨sg37785,True.intro,True.intro⟩,True.intro⟩,⟨sg37789,⟨sg37788,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37793,⟨sg37792,⟨sg37791,True.intro,True.intro⟩,True.intro⟩,⟨sg37794,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_523All : degreeTree62_523.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37773,degreeTree62_521All,degreeTree62_522All⟩

lemma degreeTree62_524All : degreeTree62_524.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37751,degreeTree62_520All,degreeTree62_523All⟩

lemma degreeTree62_525All : degreeTree62_525.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37707,degreeTree62_517All,degreeTree62_524All⟩

lemma degreeTree62_526All : degreeTree62_526.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37806,⟨sg37801,⟨sg37798,⟨sg37797,⟨sg37796,True.intro,True.intro⟩,True.intro⟩,⟨sg37800,⟨sg37799,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37804,⟨sg37803,⟨sg37802,True.intro,True.intro⟩,True.intro⟩,⟨sg37805,True.intro,True.intro⟩⟩⟩,⟨sg37812,⟨sg37809,⟨sg37808,⟨sg37807,True.intro,True.intro⟩,True.intro⟩,⟨sg37811,⟨sg37810,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37815,⟨sg37814,⟨sg37813,True.intro,True.intro⟩,True.intro⟩,⟨sg37816,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_527All : degreeTree62_527.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37828,⟨sg37823,⟨sg37820,⟨sg37819,⟨sg37818,True.intro,True.intro⟩,True.intro⟩,⟨sg37822,⟨sg37821,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37826,⟨sg37825,⟨sg37824,True.intro,True.intro⟩,True.intro⟩,⟨sg37827,True.intro,True.intro⟩⟩⟩,⟨sg37834,⟨sg37831,⟨sg37830,⟨sg37829,True.intro,True.intro⟩,True.intro⟩,⟨sg37833,⟨sg37832,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37837,⟨sg37836,⟨sg37835,True.intro,True.intro⟩,True.intro⟩,⟨sg37838,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_528All : degreeTree62_528.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37817,degreeTree62_526All,degreeTree62_527All⟩

lemma degreeTree62_529All : degreeTree62_529.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37850,⟨sg37845,⟨sg37842,⟨sg37841,⟨sg37840,True.intro,True.intro⟩,True.intro⟩,⟨sg37844,⟨sg37843,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37848,⟨sg37847,⟨sg37846,True.intro,True.intro⟩,True.intro⟩,⟨sg37849,True.intro,True.intro⟩⟩⟩,⟨sg37856,⟨sg37853,⟨sg37852,⟨sg37851,True.intro,True.intro⟩,True.intro⟩,⟨sg37855,⟨sg37854,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37859,⟨sg37858,⟨sg37857,True.intro,True.intro⟩,True.intro⟩,⟨sg37860,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_530All : degreeTree62_530.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37872,⟨sg37867,⟨sg37864,⟨sg37863,⟨sg37862,True.intro,True.intro⟩,True.intro⟩,⟨sg37866,⟨sg37865,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37870,⟨sg37869,⟨sg37868,True.intro,True.intro⟩,True.intro⟩,⟨sg37871,True.intro,True.intro⟩⟩⟩,⟨sg37878,⟨sg37875,⟨sg37874,⟨sg37873,True.intro,True.intro⟩,True.intro⟩,⟨sg37877,⟨sg37876,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37881,⟨sg37880,⟨sg37879,True.intro,True.intro⟩,True.intro⟩,⟨sg37882,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_531All : degreeTree62_531.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37861,degreeTree62_529All,degreeTree62_530All⟩

lemma degreeTree62_532All : degreeTree62_532.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37839,degreeTree62_528All,degreeTree62_531All⟩

lemma degreeTree62_533All : degreeTree62_533.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37894,⟨sg37889,⟨sg37886,⟨sg37885,⟨sg37884,True.intro,True.intro⟩,True.intro⟩,⟨sg37888,⟨sg37887,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37892,⟨sg37891,⟨sg37890,True.intro,True.intro⟩,True.intro⟩,⟨sg37893,True.intro,True.intro⟩⟩⟩,⟨sg37900,⟨sg37897,⟨sg37896,⟨sg37895,True.intro,True.intro⟩,True.intro⟩,⟨sg37899,⟨sg37898,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37903,⟨sg37902,⟨sg37901,True.intro,True.intro⟩,True.intro⟩,⟨sg37904,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_534All : degreeTree62_534.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37916,⟨sg37911,⟨sg37908,⟨sg37907,⟨sg37906,True.intro,True.intro⟩,True.intro⟩,⟨sg37910,⟨sg37909,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37914,⟨sg37913,⟨sg37912,True.intro,True.intro⟩,True.intro⟩,⟨sg37915,True.intro,True.intro⟩⟩⟩,⟨sg37922,⟨sg37919,⟨sg37918,⟨sg37917,True.intro,True.intro⟩,True.intro⟩,⟨sg37921,⟨sg37920,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37925,⟨sg37924,⟨sg37923,True.intro,True.intro⟩,True.intro⟩,⟨sg37926,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_535All : degreeTree62_535.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37905,degreeTree62_533All,degreeTree62_534All⟩

lemma degreeTree62_536All : degreeTree62_536.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37938,⟨sg37933,⟨sg37930,⟨sg37929,⟨sg37928,True.intro,True.intro⟩,True.intro⟩,⟨sg37932,⟨sg37931,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37936,⟨sg37935,⟨sg37934,True.intro,True.intro⟩,True.intro⟩,⟨sg37937,True.intro,True.intro⟩⟩⟩,⟨sg37944,⟨sg37941,⟨sg37940,⟨sg37939,True.intro,True.intro⟩,True.intro⟩,⟨sg37943,⟨sg37942,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37947,⟨sg37946,⟨sg37945,True.intro,True.intro⟩,True.intro⟩,⟨sg37948,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_537All : degreeTree62_537.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37960,⟨sg37955,⟨sg37952,⟨sg37951,⟨sg37950,True.intro,True.intro⟩,True.intro⟩,⟨sg37954,⟨sg37953,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37958,⟨sg37957,⟨sg37956,True.intro,True.intro⟩,True.intro⟩,⟨sg37959,True.intro,True.intro⟩⟩⟩,⟨sg37965,⟨sg37963,⟨sg37962,⟨sg37961,True.intro,True.intro⟩,True.intro⟩,⟨sg37964,True.intro,True.intro⟩⟩,⟨sg37968,⟨sg37967,⟨sg37966,True.intro,True.intro⟩,True.intro⟩,⟨sg37969,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_538All : degreeTree62_538.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37949,degreeTree62_536All,degreeTree62_537All⟩

lemma degreeTree62_539All : degreeTree62_539.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37927,degreeTree62_535All,degreeTree62_538All⟩

lemma degreeTree62_540All : degreeTree62_540.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37883,degreeTree62_532All,degreeTree62_539All⟩

lemma degreeTree62_541All : degreeTree62_541.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37795,degreeTree62_525All,degreeTree62_540All⟩

lemma degreeTree62_542All : degreeTree62_542.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37981,⟨sg37976,⟨sg37973,⟨sg37972,⟨sg37971,True.intro,True.intro⟩,True.intro⟩,⟨sg37975,⟨sg37974,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37979,⟨sg37978,⟨sg37977,True.intro,True.intro⟩,True.intro⟩,⟨sg37980,True.intro,True.intro⟩⟩⟩,⟨sg37987,⟨sg37984,⟨sg37983,⟨sg37982,True.intro,True.intro⟩,True.intro⟩,⟨sg37986,⟨sg37985,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg37990,⟨sg37989,⟨sg37988,True.intro,True.intro⟩,True.intro⟩,⟨sg37991,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_543All : degreeTree62_543.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38003,⟨sg37998,⟨sg37995,⟨sg37994,⟨sg37993,True.intro,True.intro⟩,True.intro⟩,⟨sg37997,⟨sg37996,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38001,⟨sg38000,⟨sg37999,True.intro,True.intro⟩,True.intro⟩,⟨sg38002,True.intro,True.intro⟩⟩⟩,⟨sg38009,⟨sg38006,⟨sg38005,⟨sg38004,True.intro,True.intro⟩,True.intro⟩,⟨sg38008,⟨sg38007,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38012,⟨sg38011,⟨sg38010,True.intro,True.intro⟩,True.intro⟩,⟨sg38013,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_544All : degreeTree62_544.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37992,degreeTree62_542All,degreeTree62_543All⟩

lemma degreeTree62_545All : degreeTree62_545.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38025,⟨sg38020,⟨sg38017,⟨sg38016,⟨sg38015,True.intro,True.intro⟩,True.intro⟩,⟨sg38019,⟨sg38018,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38023,⟨sg38022,⟨sg38021,True.intro,True.intro⟩,True.intro⟩,⟨sg38024,True.intro,True.intro⟩⟩⟩,⟨sg38031,⟨sg38028,⟨sg38027,⟨sg38026,True.intro,True.intro⟩,True.intro⟩,⟨sg38030,⟨sg38029,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38034,⟨sg38033,⟨sg38032,True.intro,True.intro⟩,True.intro⟩,⟨sg38035,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_546All : degreeTree62_546.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38047,⟨sg38042,⟨sg38039,⟨sg38038,⟨sg38037,True.intro,True.intro⟩,True.intro⟩,⟨sg38041,⟨sg38040,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38045,⟨sg38044,⟨sg38043,True.intro,True.intro⟩,True.intro⟩,⟨sg38046,True.intro,True.intro⟩⟩⟩,⟨sg38053,⟨sg38050,⟨sg38049,⟨sg38048,True.intro,True.intro⟩,True.intro⟩,⟨sg38052,⟨sg38051,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38056,⟨sg38055,⟨sg38054,True.intro,True.intro⟩,True.intro⟩,⟨sg38057,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_547All : degreeTree62_547.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38036,degreeTree62_545All,degreeTree62_546All⟩

lemma degreeTree62_548All : degreeTree62_548.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38014,degreeTree62_544All,degreeTree62_547All⟩

lemma degreeTree62_549All : degreeTree62_549.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38069,⟨sg38064,⟨sg38061,⟨sg38060,⟨sg38059,True.intro,True.intro⟩,True.intro⟩,⟨sg38063,⟨sg38062,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38067,⟨sg38066,⟨sg38065,True.intro,True.intro⟩,True.intro⟩,⟨sg38068,True.intro,True.intro⟩⟩⟩,⟨sg38075,⟨sg38072,⟨sg38071,⟨sg38070,True.intro,True.intro⟩,True.intro⟩,⟨sg38074,⟨sg38073,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38078,⟨sg38077,⟨sg38076,True.intro,True.intro⟩,True.intro⟩,⟨sg38079,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_550All : degreeTree62_550.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38091,⟨sg38086,⟨sg38083,⟨sg38082,⟨sg38081,True.intro,True.intro⟩,True.intro⟩,⟨sg38085,⟨sg38084,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38089,⟨sg38088,⟨sg38087,True.intro,True.intro⟩,True.intro⟩,⟨sg38090,True.intro,True.intro⟩⟩⟩,⟨sg38097,⟨sg38094,⟨sg38093,⟨sg38092,True.intro,True.intro⟩,True.intro⟩,⟨sg38096,⟨sg38095,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38100,⟨sg38099,⟨sg38098,True.intro,True.intro⟩,True.intro⟩,⟨sg38101,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_551All : degreeTree62_551.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38080,degreeTree62_549All,degreeTree62_550All⟩

lemma degreeTree62_552All : degreeTree62_552.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38113,⟨sg38108,⟨sg38105,⟨sg38104,⟨sg38103,True.intro,True.intro⟩,True.intro⟩,⟨sg38107,⟨sg38106,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38111,⟨sg38110,⟨sg38109,True.intro,True.intro⟩,True.intro⟩,⟨sg38112,True.intro,True.intro⟩⟩⟩,⟨sg38119,⟨sg38116,⟨sg38115,⟨sg38114,True.intro,True.intro⟩,True.intro⟩,⟨sg38118,⟨sg38117,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38122,⟨sg38121,⟨sg38120,True.intro,True.intro⟩,True.intro⟩,⟨sg38123,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_553All : degreeTree62_553.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38135,⟨sg38130,⟨sg38127,⟨sg38126,⟨sg38125,True.intro,True.intro⟩,True.intro⟩,⟨sg38129,⟨sg38128,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38133,⟨sg38132,⟨sg38131,True.intro,True.intro⟩,True.intro⟩,⟨sg38134,True.intro,True.intro⟩⟩⟩,⟨sg38141,⟨sg38138,⟨sg38137,⟨sg38136,True.intro,True.intro⟩,True.intro⟩,⟨sg38140,⟨sg38139,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38144,⟨sg38143,⟨sg38142,True.intro,True.intro⟩,True.intro⟩,⟨sg38145,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_554All : degreeTree62_554.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38124,degreeTree62_552All,degreeTree62_553All⟩

lemma degreeTree62_555All : degreeTree62_555.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38102,degreeTree62_551All,degreeTree62_554All⟩

lemma degreeTree62_556All : degreeTree62_556.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38058,degreeTree62_548All,degreeTree62_555All⟩

lemma degreeTree62_557All : degreeTree62_557.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38157,⟨sg38152,⟨sg38149,⟨sg38148,⟨sg38147,True.intro,True.intro⟩,True.intro⟩,⟨sg38151,⟨sg38150,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38155,⟨sg38154,⟨sg38153,True.intro,True.intro⟩,True.intro⟩,⟨sg38156,True.intro,True.intro⟩⟩⟩,⟨sg38163,⟨sg38160,⟨sg38159,⟨sg38158,True.intro,True.intro⟩,True.intro⟩,⟨sg38162,⟨sg38161,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38166,⟨sg38165,⟨sg38164,True.intro,True.intro⟩,True.intro⟩,⟨sg38167,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_558All : degreeTree62_558.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38179,⟨sg38174,⟨sg38171,⟨sg38170,⟨sg38169,True.intro,True.intro⟩,True.intro⟩,⟨sg38173,⟨sg38172,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38177,⟨sg38176,⟨sg38175,True.intro,True.intro⟩,True.intro⟩,⟨sg38178,True.intro,True.intro⟩⟩⟩,⟨sg38185,⟨sg38182,⟨sg38181,⟨sg38180,True.intro,True.intro⟩,True.intro⟩,⟨sg38184,⟨sg38183,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38188,⟨sg38187,⟨sg38186,True.intro,True.intro⟩,True.intro⟩,⟨sg38189,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_559All : degreeTree62_559.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38168,degreeTree62_557All,degreeTree62_558All⟩

lemma degreeTree62_560All : degreeTree62_560.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38201,⟨sg38196,⟨sg38193,⟨sg38192,⟨sg38191,True.intro,True.intro⟩,True.intro⟩,⟨sg38195,⟨sg38194,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38199,⟨sg38198,⟨sg38197,True.intro,True.intro⟩,True.intro⟩,⟨sg38200,True.intro,True.intro⟩⟩⟩,⟨sg38207,⟨sg38204,⟨sg38203,⟨sg38202,True.intro,True.intro⟩,True.intro⟩,⟨sg38206,⟨sg38205,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38210,⟨sg38209,⟨sg38208,True.intro,True.intro⟩,True.intro⟩,⟨sg38211,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_561All : degreeTree62_561.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38223,⟨sg38218,⟨sg38215,⟨sg38214,⟨sg38213,True.intro,True.intro⟩,True.intro⟩,⟨sg38217,⟨sg38216,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38221,⟨sg38220,⟨sg38219,True.intro,True.intro⟩,True.intro⟩,⟨sg38222,True.intro,True.intro⟩⟩⟩,⟨sg38229,⟨sg38226,⟨sg38225,⟨sg38224,True.intro,True.intro⟩,True.intro⟩,⟨sg38228,⟨sg38227,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38232,⟨sg38231,⟨sg38230,True.intro,True.intro⟩,True.intro⟩,⟨sg38233,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_562All : degreeTree62_562.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38212,degreeTree62_560All,degreeTree62_561All⟩

lemma degreeTree62_563All : degreeTree62_563.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38190,degreeTree62_559All,degreeTree62_562All⟩

lemma degreeTree62_564All : degreeTree62_564.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38245,⟨sg38240,⟨sg38237,⟨sg38236,⟨sg38235,True.intro,True.intro⟩,True.intro⟩,⟨sg38239,⟨sg38238,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38243,⟨sg38242,⟨sg38241,True.intro,True.intro⟩,True.intro⟩,⟨sg38244,True.intro,True.intro⟩⟩⟩,⟨sg38251,⟨sg38248,⟨sg38247,⟨sg38246,True.intro,True.intro⟩,True.intro⟩,⟨sg38250,⟨sg38249,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38254,⟨sg38253,⟨sg38252,True.intro,True.intro⟩,True.intro⟩,⟨sg38255,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_565All : degreeTree62_565.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38267,⟨sg38262,⟨sg38259,⟨sg38258,⟨sg38257,True.intro,True.intro⟩,True.intro⟩,⟨sg38261,⟨sg38260,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38265,⟨sg38264,⟨sg38263,True.intro,True.intro⟩,True.intro⟩,⟨sg38266,True.intro,True.intro⟩⟩⟩,⟨sg38273,⟨sg38270,⟨sg38269,⟨sg38268,True.intro,True.intro⟩,True.intro⟩,⟨sg38272,⟨sg38271,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38276,⟨sg38275,⟨sg38274,True.intro,True.intro⟩,True.intro⟩,⟨sg38277,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_566All : degreeTree62_566.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38256,degreeTree62_564All,degreeTree62_565All⟩

lemma degreeTree62_567All : degreeTree62_567.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38289,⟨sg38284,⟨sg38281,⟨sg38280,⟨sg38279,True.intro,True.intro⟩,True.intro⟩,⟨sg38283,⟨sg38282,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38287,⟨sg38286,⟨sg38285,True.intro,True.intro⟩,True.intro⟩,⟨sg38288,True.intro,True.intro⟩⟩⟩,⟨sg38295,⟨sg38292,⟨sg38291,⟨sg38290,True.intro,True.intro⟩,True.intro⟩,⟨sg38294,⟨sg38293,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38298,⟨sg38297,⟨sg38296,True.intro,True.intro⟩,True.intro⟩,⟨sg38299,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_568All : degreeTree62_568.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38311,⟨sg38306,⟨sg38303,⟨sg38302,⟨sg38301,True.intro,True.intro⟩,True.intro⟩,⟨sg38305,⟨sg38304,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38309,⟨sg38308,⟨sg38307,True.intro,True.intro⟩,True.intro⟩,⟨sg38310,True.intro,True.intro⟩⟩⟩,⟨sg38316,⟨sg38314,⟨sg38313,⟨sg38312,True.intro,True.intro⟩,True.intro⟩,⟨sg38315,True.intro,True.intro⟩⟩,⟨sg38319,⟨sg38318,⟨sg38317,True.intro,True.intro⟩,True.intro⟩,⟨sg38320,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_569All : degreeTree62_569.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38300,degreeTree62_567All,degreeTree62_568All⟩

lemma degreeTree62_570All : degreeTree62_570.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38278,degreeTree62_566All,degreeTree62_569All⟩

lemma degreeTree62_571All : degreeTree62_571.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38234,degreeTree62_563All,degreeTree62_570All⟩

lemma degreeTree62_572All : degreeTree62_572.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38146,degreeTree62_556All,degreeTree62_571All⟩

lemma degreeTree62_573All : degreeTree62_573.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37970,degreeTree62_541All,degreeTree62_572All⟩

lemma degreeTree62_574All : degreeTree62_574.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38332,⟨sg38327,⟨sg38324,⟨sg38323,⟨sg38322,True.intro,True.intro⟩,True.intro⟩,⟨sg38326,⟨sg38325,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38330,⟨sg38329,⟨sg38328,True.intro,True.intro⟩,True.intro⟩,⟨sg38331,True.intro,True.intro⟩⟩⟩,⟨sg38338,⟨sg38335,⟨sg38334,⟨sg38333,True.intro,True.intro⟩,True.intro⟩,⟨sg38337,⟨sg38336,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38341,⟨sg38340,⟨sg38339,True.intro,True.intro⟩,True.intro⟩,⟨sg38342,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_575All : degreeTree62_575.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38354,⟨sg38349,⟨sg38346,⟨sg38345,⟨sg38344,True.intro,True.intro⟩,True.intro⟩,⟨sg38348,⟨sg38347,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38352,⟨sg38351,⟨sg38350,True.intro,True.intro⟩,True.intro⟩,⟨sg38353,True.intro,True.intro⟩⟩⟩,⟨sg38360,⟨sg38357,⟨sg38356,⟨sg38355,True.intro,True.intro⟩,True.intro⟩,⟨sg38359,⟨sg38358,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38363,⟨sg38362,⟨sg38361,True.intro,True.intro⟩,True.intro⟩,⟨sg38364,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_576All : degreeTree62_576.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38343,degreeTree62_574All,degreeTree62_575All⟩

lemma degreeTree62_577All : degreeTree62_577.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38376,⟨sg38371,⟨sg38368,⟨sg38367,⟨sg38366,True.intro,True.intro⟩,True.intro⟩,⟨sg38370,⟨sg38369,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38374,⟨sg38373,⟨sg38372,True.intro,True.intro⟩,True.intro⟩,⟨sg38375,True.intro,True.intro⟩⟩⟩,⟨sg38382,⟨sg38379,⟨sg38378,⟨sg38377,True.intro,True.intro⟩,True.intro⟩,⟨sg38381,⟨sg38380,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38385,⟨sg38384,⟨sg38383,True.intro,True.intro⟩,True.intro⟩,⟨sg38386,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_578All : degreeTree62_578.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38398,⟨sg38393,⟨sg38390,⟨sg38389,⟨sg38388,True.intro,True.intro⟩,True.intro⟩,⟨sg38392,⟨sg38391,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38396,⟨sg38395,⟨sg38394,True.intro,True.intro⟩,True.intro⟩,⟨sg38397,True.intro,True.intro⟩⟩⟩,⟨sg38404,⟨sg38401,⟨sg38400,⟨sg38399,True.intro,True.intro⟩,True.intro⟩,⟨sg38403,⟨sg38402,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38407,⟨sg38406,⟨sg38405,True.intro,True.intro⟩,True.intro⟩,⟨sg38408,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_579All : degreeTree62_579.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38387,degreeTree62_577All,degreeTree62_578All⟩

lemma degreeTree62_580All : degreeTree62_580.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38365,degreeTree62_576All,degreeTree62_579All⟩

lemma degreeTree62_581All : degreeTree62_581.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38420,⟨sg38415,⟨sg38412,⟨sg38411,⟨sg38410,True.intro,True.intro⟩,True.intro⟩,⟨sg38414,⟨sg38413,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38418,⟨sg38417,⟨sg38416,True.intro,True.intro⟩,True.intro⟩,⟨sg38419,True.intro,True.intro⟩⟩⟩,⟨sg38426,⟨sg38423,⟨sg38422,⟨sg38421,True.intro,True.intro⟩,True.intro⟩,⟨sg38425,⟨sg38424,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38429,⟨sg38428,⟨sg38427,True.intro,True.intro⟩,True.intro⟩,⟨sg38430,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_582All : degreeTree62_582.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38442,⟨sg38437,⟨sg38434,⟨sg38433,⟨sg38432,True.intro,True.intro⟩,True.intro⟩,⟨sg38436,⟨sg38435,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38440,⟨sg38439,⟨sg38438,True.intro,True.intro⟩,True.intro⟩,⟨sg38441,True.intro,True.intro⟩⟩⟩,⟨sg38448,⟨sg38445,⟨sg38444,⟨sg38443,True.intro,True.intro⟩,True.intro⟩,⟨sg38447,⟨sg38446,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38451,⟨sg38450,⟨sg38449,True.intro,True.intro⟩,True.intro⟩,⟨sg38452,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_583All : degreeTree62_583.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38431,degreeTree62_581All,degreeTree62_582All⟩

lemma degreeTree62_584All : degreeTree62_584.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38464,⟨sg38459,⟨sg38456,⟨sg38455,⟨sg38454,True.intro,True.intro⟩,True.intro⟩,⟨sg38458,⟨sg38457,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38462,⟨sg38461,⟨sg38460,True.intro,True.intro⟩,True.intro⟩,⟨sg38463,True.intro,True.intro⟩⟩⟩,⟨sg38470,⟨sg38467,⟨sg38466,⟨sg38465,True.intro,True.intro⟩,True.intro⟩,⟨sg38469,⟨sg38468,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38473,⟨sg38472,⟨sg38471,True.intro,True.intro⟩,True.intro⟩,⟨sg38474,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_585All : degreeTree62_585.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38486,⟨sg38481,⟨sg38478,⟨sg38477,⟨sg38476,True.intro,True.intro⟩,True.intro⟩,⟨sg38480,⟨sg38479,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38484,⟨sg38483,⟨sg38482,True.intro,True.intro⟩,True.intro⟩,⟨sg38485,True.intro,True.intro⟩⟩⟩,⟨sg38492,⟨sg38489,⟨sg38488,⟨sg38487,True.intro,True.intro⟩,True.intro⟩,⟨sg38491,⟨sg38490,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38495,⟨sg38494,⟨sg38493,True.intro,True.intro⟩,True.intro⟩,⟨sg38496,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_586All : degreeTree62_586.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38475,degreeTree62_584All,degreeTree62_585All⟩

lemma degreeTree62_587All : degreeTree62_587.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38453,degreeTree62_583All,degreeTree62_586All⟩

lemma degreeTree62_588All : degreeTree62_588.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38409,degreeTree62_580All,degreeTree62_587All⟩

lemma degreeTree62_589All : degreeTree62_589.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38508,⟨sg38503,⟨sg38500,⟨sg38499,⟨sg38498,True.intro,True.intro⟩,True.intro⟩,⟨sg38502,⟨sg38501,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38506,⟨sg38505,⟨sg38504,True.intro,True.intro⟩,True.intro⟩,⟨sg38507,True.intro,True.intro⟩⟩⟩,⟨sg38514,⟨sg38511,⟨sg38510,⟨sg38509,True.intro,True.intro⟩,True.intro⟩,⟨sg38513,⟨sg38512,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38517,⟨sg38516,⟨sg38515,True.intro,True.intro⟩,True.intro⟩,⟨sg38518,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_590All : degreeTree62_590.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38530,⟨sg38525,⟨sg38522,⟨sg38521,⟨sg38520,True.intro,True.intro⟩,True.intro⟩,⟨sg38524,⟨sg38523,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38528,⟨sg38527,⟨sg38526,True.intro,True.intro⟩,True.intro⟩,⟨sg38529,True.intro,True.intro⟩⟩⟩,⟨sg38536,⟨sg38533,⟨sg38532,⟨sg38531,True.intro,True.intro⟩,True.intro⟩,⟨sg38535,⟨sg38534,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38539,⟨sg38538,⟨sg38537,True.intro,True.intro⟩,True.intro⟩,⟨sg38540,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_591All : degreeTree62_591.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38519,degreeTree62_589All,degreeTree62_590All⟩

lemma degreeTree62_592All : degreeTree62_592.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38552,⟨sg38547,⟨sg38544,⟨sg38543,⟨sg38542,True.intro,True.intro⟩,True.intro⟩,⟨sg38546,⟨sg38545,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38550,⟨sg38549,⟨sg38548,True.intro,True.intro⟩,True.intro⟩,⟨sg38551,True.intro,True.intro⟩⟩⟩,⟨sg38558,⟨sg38555,⟨sg38554,⟨sg38553,True.intro,True.intro⟩,True.intro⟩,⟨sg38557,⟨sg38556,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38561,⟨sg38560,⟨sg38559,True.intro,True.intro⟩,True.intro⟩,⟨sg38562,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_593All : degreeTree62_593.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38574,⟨sg38569,⟨sg38566,⟨sg38565,⟨sg38564,True.intro,True.intro⟩,True.intro⟩,⟨sg38568,⟨sg38567,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38572,⟨sg38571,⟨sg38570,True.intro,True.intro⟩,True.intro⟩,⟨sg38573,True.intro,True.intro⟩⟩⟩,⟨sg38580,⟨sg38577,⟨sg38576,⟨sg38575,True.intro,True.intro⟩,True.intro⟩,⟨sg38579,⟨sg38578,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38583,⟨sg38582,⟨sg38581,True.intro,True.intro⟩,True.intro⟩,⟨sg38584,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_594All : degreeTree62_594.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38563,degreeTree62_592All,degreeTree62_593All⟩

lemma degreeTree62_595All : degreeTree62_595.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38541,degreeTree62_591All,degreeTree62_594All⟩

lemma degreeTree62_596All : degreeTree62_596.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38596,⟨sg38591,⟨sg38588,⟨sg38587,⟨sg38586,True.intro,True.intro⟩,True.intro⟩,⟨sg38590,⟨sg38589,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38594,⟨sg38593,⟨sg38592,True.intro,True.intro⟩,True.intro⟩,⟨sg38595,True.intro,True.intro⟩⟩⟩,⟨sg38602,⟨sg38599,⟨sg38598,⟨sg38597,True.intro,True.intro⟩,True.intro⟩,⟨sg38601,⟨sg38600,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38605,⟨sg38604,⟨sg38603,True.intro,True.intro⟩,True.intro⟩,⟨sg38606,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_597All : degreeTree62_597.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38618,⟨sg38613,⟨sg38610,⟨sg38609,⟨sg38608,True.intro,True.intro⟩,True.intro⟩,⟨sg38612,⟨sg38611,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38616,⟨sg38615,⟨sg38614,True.intro,True.intro⟩,True.intro⟩,⟨sg38617,True.intro,True.intro⟩⟩⟩,⟨sg38624,⟨sg38621,⟨sg38620,⟨sg38619,True.intro,True.intro⟩,True.intro⟩,⟨sg38623,⟨sg38622,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38627,⟨sg38626,⟨sg38625,True.intro,True.intro⟩,True.intro⟩,⟨sg38628,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_598All : degreeTree62_598.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38607,degreeTree62_596All,degreeTree62_597All⟩

lemma degreeTree62_599All : degreeTree62_599.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38640,⟨sg38635,⟨sg38632,⟨sg38631,⟨sg38630,True.intro,True.intro⟩,True.intro⟩,⟨sg38634,⟨sg38633,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38638,⟨sg38637,⟨sg38636,True.intro,True.intro⟩,True.intro⟩,⟨sg38639,True.intro,True.intro⟩⟩⟩,⟨sg38646,⟨sg38643,⟨sg38642,⟨sg38641,True.intro,True.intro⟩,True.intro⟩,⟨sg38645,⟨sg38644,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38649,⟨sg38648,⟨sg38647,True.intro,True.intro⟩,True.intro⟩,⟨sg38650,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_600All : degreeTree62_600.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38662,⟨sg38657,⟨sg38654,⟨sg38653,⟨sg38652,True.intro,True.intro⟩,True.intro⟩,⟨sg38656,⟨sg38655,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38660,⟨sg38659,⟨sg38658,True.intro,True.intro⟩,True.intro⟩,⟨sg38661,True.intro,True.intro⟩⟩⟩,⟨sg38667,⟨sg38665,⟨sg38664,⟨sg38663,True.intro,True.intro⟩,True.intro⟩,⟨sg38666,True.intro,True.intro⟩⟩,⟨sg38670,⟨sg38669,⟨sg38668,True.intro,True.intro⟩,True.intro⟩,⟨sg38671,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_601All : degreeTree62_601.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38651,degreeTree62_599All,degreeTree62_600All⟩

lemma degreeTree62_602All : degreeTree62_602.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38629,degreeTree62_598All,degreeTree62_601All⟩

lemma degreeTree62_603All : degreeTree62_603.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38585,degreeTree62_595All,degreeTree62_602All⟩

lemma degreeTree62_604All : degreeTree62_604.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38497,degreeTree62_588All,degreeTree62_603All⟩

lemma degreeTree62_605All : degreeTree62_605.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38683,⟨sg38678,⟨sg38675,⟨sg38674,⟨sg38673,True.intro,True.intro⟩,True.intro⟩,⟨sg38677,⟨sg38676,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38681,⟨sg38680,⟨sg38679,True.intro,True.intro⟩,True.intro⟩,⟨sg38682,True.intro,True.intro⟩⟩⟩,⟨sg38689,⟨sg38686,⟨sg38685,⟨sg38684,True.intro,True.intro⟩,True.intro⟩,⟨sg38688,⟨sg38687,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38692,⟨sg38691,⟨sg38690,True.intro,True.intro⟩,True.intro⟩,⟨sg38693,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_606All : degreeTree62_606.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38705,⟨sg38700,⟨sg38697,⟨sg38696,⟨sg38695,True.intro,True.intro⟩,True.intro⟩,⟨sg38699,⟨sg38698,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38703,⟨sg38702,⟨sg38701,True.intro,True.intro⟩,True.intro⟩,⟨sg38704,True.intro,True.intro⟩⟩⟩,⟨sg38711,⟨sg38708,⟨sg38707,⟨sg38706,True.intro,True.intro⟩,True.intro⟩,⟨sg38710,⟨sg38709,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38714,⟨sg38713,⟨sg38712,True.intro,True.intro⟩,True.intro⟩,⟨sg38715,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_607All : degreeTree62_607.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38694,degreeTree62_605All,degreeTree62_606All⟩

lemma degreeTree62_608All : degreeTree62_608.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38727,⟨sg38722,⟨sg38719,⟨sg38718,⟨sg38717,True.intro,True.intro⟩,True.intro⟩,⟨sg38721,⟨sg38720,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38725,⟨sg38724,⟨sg38723,True.intro,True.intro⟩,True.intro⟩,⟨sg38726,True.intro,True.intro⟩⟩⟩,⟨sg38733,⟨sg38730,⟨sg38729,⟨sg38728,True.intro,True.intro⟩,True.intro⟩,⟨sg38732,⟨sg38731,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38736,⟨sg38735,⟨sg38734,True.intro,True.intro⟩,True.intro⟩,⟨sg38737,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_609All : degreeTree62_609.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38749,⟨sg38744,⟨sg38741,⟨sg38740,⟨sg38739,True.intro,True.intro⟩,True.intro⟩,⟨sg38743,⟨sg38742,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38747,⟨sg38746,⟨sg38745,True.intro,True.intro⟩,True.intro⟩,⟨sg38748,True.intro,True.intro⟩⟩⟩,⟨sg38755,⟨sg38752,⟨sg38751,⟨sg38750,True.intro,True.intro⟩,True.intro⟩,⟨sg38754,⟨sg38753,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38758,⟨sg38757,⟨sg38756,True.intro,True.intro⟩,True.intro⟩,⟨sg38759,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_610All : degreeTree62_610.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38738,degreeTree62_608All,degreeTree62_609All⟩

lemma degreeTree62_611All : degreeTree62_611.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38716,degreeTree62_607All,degreeTree62_610All⟩

lemma degreeTree62_612All : degreeTree62_612.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38771,⟨sg38766,⟨sg38763,⟨sg38762,⟨sg38761,True.intro,True.intro⟩,True.intro⟩,⟨sg38765,⟨sg38764,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38769,⟨sg38768,⟨sg38767,True.intro,True.intro⟩,True.intro⟩,⟨sg38770,True.intro,True.intro⟩⟩⟩,⟨sg38777,⟨sg38774,⟨sg38773,⟨sg38772,True.intro,True.intro⟩,True.intro⟩,⟨sg38776,⟨sg38775,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38780,⟨sg38779,⟨sg38778,True.intro,True.intro⟩,True.intro⟩,⟨sg38781,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_613All : degreeTree62_613.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38793,⟨sg38788,⟨sg38785,⟨sg38784,⟨sg38783,True.intro,True.intro⟩,True.intro⟩,⟨sg38787,⟨sg38786,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38791,⟨sg38790,⟨sg38789,True.intro,True.intro⟩,True.intro⟩,⟨sg38792,True.intro,True.intro⟩⟩⟩,⟨sg38799,⟨sg38796,⟨sg38795,⟨sg38794,True.intro,True.intro⟩,True.intro⟩,⟨sg38798,⟨sg38797,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38802,⟨sg38801,⟨sg38800,True.intro,True.intro⟩,True.intro⟩,⟨sg38803,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_614All : degreeTree62_614.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38782,degreeTree62_612All,degreeTree62_613All⟩

lemma degreeTree62_615All : degreeTree62_615.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38815,⟨sg38810,⟨sg38807,⟨sg38806,⟨sg38805,True.intro,True.intro⟩,True.intro⟩,⟨sg38809,⟨sg38808,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38813,⟨sg38812,⟨sg38811,True.intro,True.intro⟩,True.intro⟩,⟨sg38814,True.intro,True.intro⟩⟩⟩,⟨sg38821,⟨sg38818,⟨sg38817,⟨sg38816,True.intro,True.intro⟩,True.intro⟩,⟨sg38820,⟨sg38819,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38824,⟨sg38823,⟨sg38822,True.intro,True.intro⟩,True.intro⟩,⟨sg38825,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_616All : degreeTree62_616.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38837,⟨sg38832,⟨sg38829,⟨sg38828,⟨sg38827,True.intro,True.intro⟩,True.intro⟩,⟨sg38831,⟨sg38830,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38835,⟨sg38834,⟨sg38833,True.intro,True.intro⟩,True.intro⟩,⟨sg38836,True.intro,True.intro⟩⟩⟩,⟨sg38843,⟨sg38840,⟨sg38839,⟨sg38838,True.intro,True.intro⟩,True.intro⟩,⟨sg38842,⟨sg38841,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38846,⟨sg38845,⟨sg38844,True.intro,True.intro⟩,True.intro⟩,⟨sg38847,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_617All : degreeTree62_617.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38826,degreeTree62_615All,degreeTree62_616All⟩

lemma degreeTree62_618All : degreeTree62_618.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38804,degreeTree62_614All,degreeTree62_617All⟩

lemma degreeTree62_619All : degreeTree62_619.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38760,degreeTree62_611All,degreeTree62_618All⟩

lemma degreeTree62_620All : degreeTree62_620.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38859,⟨sg38854,⟨sg38851,⟨sg38850,⟨sg38849,True.intro,True.intro⟩,True.intro⟩,⟨sg38853,⟨sg38852,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38857,⟨sg38856,⟨sg38855,True.intro,True.intro⟩,True.intro⟩,⟨sg38858,True.intro,True.intro⟩⟩⟩,⟨sg38865,⟨sg38862,⟨sg38861,⟨sg38860,True.intro,True.intro⟩,True.intro⟩,⟨sg38864,⟨sg38863,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38868,⟨sg38867,⟨sg38866,True.intro,True.intro⟩,True.intro⟩,⟨sg38869,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_621All : degreeTree62_621.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38881,⟨sg38876,⟨sg38873,⟨sg38872,⟨sg38871,True.intro,True.intro⟩,True.intro⟩,⟨sg38875,⟨sg38874,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38879,⟨sg38878,⟨sg38877,True.intro,True.intro⟩,True.intro⟩,⟨sg38880,True.intro,True.intro⟩⟩⟩,⟨sg38887,⟨sg38884,⟨sg38883,⟨sg38882,True.intro,True.intro⟩,True.intro⟩,⟨sg38886,⟨sg38885,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38890,⟨sg38889,⟨sg38888,True.intro,True.intro⟩,True.intro⟩,⟨sg38891,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_622All : degreeTree62_622.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38870,degreeTree62_620All,degreeTree62_621All⟩

lemma degreeTree62_623All : degreeTree62_623.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38903,⟨sg38898,⟨sg38895,⟨sg38894,⟨sg38893,True.intro,True.intro⟩,True.intro⟩,⟨sg38897,⟨sg38896,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38901,⟨sg38900,⟨sg38899,True.intro,True.intro⟩,True.intro⟩,⟨sg38902,True.intro,True.intro⟩⟩⟩,⟨sg38909,⟨sg38906,⟨sg38905,⟨sg38904,True.intro,True.intro⟩,True.intro⟩,⟨sg38908,⟨sg38907,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38912,⟨sg38911,⟨sg38910,True.intro,True.intro⟩,True.intro⟩,⟨sg38913,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_624All : degreeTree62_624.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38925,⟨sg38920,⟨sg38917,⟨sg38916,⟨sg38915,True.intro,True.intro⟩,True.intro⟩,⟨sg38919,⟨sg38918,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38923,⟨sg38922,⟨sg38921,True.intro,True.intro⟩,True.intro⟩,⟨sg38924,True.intro,True.intro⟩⟩⟩,⟨sg38931,⟨sg38928,⟨sg38927,⟨sg38926,True.intro,True.intro⟩,True.intro⟩,⟨sg38930,⟨sg38929,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38934,⟨sg38933,⟨sg38932,True.intro,True.intro⟩,True.intro⟩,⟨sg38935,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_625All : degreeTree62_625.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38914,degreeTree62_623All,degreeTree62_624All⟩

lemma degreeTree62_626All : degreeTree62_626.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38892,degreeTree62_622All,degreeTree62_625All⟩

lemma degreeTree62_627All : degreeTree62_627.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38947,⟨sg38942,⟨sg38939,⟨sg38938,⟨sg38937,True.intro,True.intro⟩,True.intro⟩,⟨sg38941,⟨sg38940,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38945,⟨sg38944,⟨sg38943,True.intro,True.intro⟩,True.intro⟩,⟨sg38946,True.intro,True.intro⟩⟩⟩,⟨sg38953,⟨sg38950,⟨sg38949,⟨sg38948,True.intro,True.intro⟩,True.intro⟩,⟨sg38952,⟨sg38951,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38956,⟨sg38955,⟨sg38954,True.intro,True.intro⟩,True.intro⟩,⟨sg38957,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_628All : degreeTree62_628.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38969,⟨sg38964,⟨sg38961,⟨sg38960,⟨sg38959,True.intro,True.intro⟩,True.intro⟩,⟨sg38963,⟨sg38962,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38967,⟨sg38966,⟨sg38965,True.intro,True.intro⟩,True.intro⟩,⟨sg38968,True.intro,True.intro⟩⟩⟩,⟨sg38975,⟨sg38972,⟨sg38971,⟨sg38970,True.intro,True.intro⟩,True.intro⟩,⟨sg38974,⟨sg38973,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38978,⟨sg38977,⟨sg38976,True.intro,True.intro⟩,True.intro⟩,⟨sg38979,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_629All : degreeTree62_629.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38958,degreeTree62_627All,degreeTree62_628All⟩

lemma degreeTree62_630All : degreeTree62_630.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38991,⟨sg38986,⟨sg38983,⟨sg38982,⟨sg38981,True.intro,True.intro⟩,True.intro⟩,⟨sg38985,⟨sg38984,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg38989,⟨sg38988,⟨sg38987,True.intro,True.intro⟩,True.intro⟩,⟨sg38990,True.intro,True.intro⟩⟩⟩,⟨sg38997,⟨sg38994,⟨sg38993,⟨sg38992,True.intro,True.intro⟩,True.intro⟩,⟨sg38996,⟨sg38995,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39000,⟨sg38999,⟨sg38998,True.intro,True.intro⟩,True.intro⟩,⟨sg39001,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_631All : degreeTree62_631.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39013,⟨sg39008,⟨sg39005,⟨sg39004,⟨sg39003,True.intro,True.intro⟩,True.intro⟩,⟨sg39007,⟨sg39006,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39011,⟨sg39010,⟨sg39009,True.intro,True.intro⟩,True.intro⟩,⟨sg39012,True.intro,True.intro⟩⟩⟩,⟨sg39018,⟨sg39016,⟨sg39015,⟨sg39014,True.intro,True.intro⟩,True.intro⟩,⟨sg39017,True.intro,True.intro⟩⟩,⟨sg39021,⟨sg39020,⟨sg39019,True.intro,True.intro⟩,True.intro⟩,⟨sg39022,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_632All : degreeTree62_632.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39002,degreeTree62_630All,degreeTree62_631All⟩

lemma degreeTree62_633All : degreeTree62_633.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38980,degreeTree62_629All,degreeTree62_632All⟩

lemma degreeTree62_634All : degreeTree62_634.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38936,degreeTree62_626All,degreeTree62_633All⟩

lemma degreeTree62_635All : degreeTree62_635.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38848,degreeTree62_619All,degreeTree62_634All⟩

lemma degreeTree62_636All : degreeTree62_636.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38672,degreeTree62_604All,degreeTree62_635All⟩

lemma degreeTree62_637All : degreeTree62_637.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg38321,degreeTree62_573All,degreeTree62_636All⟩

lemma degreeTree62_638All : degreeTree62_638.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39034,⟨sg39029,⟨sg39026,⟨sg39025,⟨sg39024,True.intro,True.intro⟩,True.intro⟩,⟨sg39028,⟨sg39027,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39032,⟨sg39031,⟨sg39030,True.intro,True.intro⟩,True.intro⟩,⟨sg39033,True.intro,True.intro⟩⟩⟩,⟨sg39040,⟨sg39037,⟨sg39036,⟨sg39035,True.intro,True.intro⟩,True.intro⟩,⟨sg39039,⟨sg39038,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39043,⟨sg39042,⟨sg39041,True.intro,True.intro⟩,True.intro⟩,⟨sg39044,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_639All : degreeTree62_639.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39056,⟨sg39051,⟨sg39048,⟨sg39047,⟨sg39046,True.intro,True.intro⟩,True.intro⟩,⟨sg39050,⟨sg39049,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39054,⟨sg39053,⟨sg39052,True.intro,True.intro⟩,True.intro⟩,⟨sg39055,True.intro,True.intro⟩⟩⟩,⟨sg39062,⟨sg39059,⟨sg39058,⟨sg39057,True.intro,True.intro⟩,True.intro⟩,⟨sg39061,⟨sg39060,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39065,⟨sg39064,⟨sg39063,True.intro,True.intro⟩,True.intro⟩,⟨sg39066,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_640All : degreeTree62_640.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39045,degreeTree62_638All,degreeTree62_639All⟩

lemma degreeTree62_641All : degreeTree62_641.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39078,⟨sg39073,⟨sg39070,⟨sg39069,⟨sg39068,True.intro,True.intro⟩,True.intro⟩,⟨sg39072,⟨sg39071,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39076,⟨sg39075,⟨sg39074,True.intro,True.intro⟩,True.intro⟩,⟨sg39077,True.intro,True.intro⟩⟩⟩,⟨sg39084,⟨sg39081,⟨sg39080,⟨sg39079,True.intro,True.intro⟩,True.intro⟩,⟨sg39083,⟨sg39082,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39087,⟨sg39086,⟨sg39085,True.intro,True.intro⟩,True.intro⟩,⟨sg39088,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_642All : degreeTree62_642.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39100,⟨sg39095,⟨sg39092,⟨sg39091,⟨sg39090,True.intro,True.intro⟩,True.intro⟩,⟨sg39094,⟨sg39093,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39098,⟨sg39097,⟨sg39096,True.intro,True.intro⟩,True.intro⟩,⟨sg39099,True.intro,True.intro⟩⟩⟩,⟨sg39106,⟨sg39103,⟨sg39102,⟨sg39101,True.intro,True.intro⟩,True.intro⟩,⟨sg39105,⟨sg39104,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39109,⟨sg39108,⟨sg39107,True.intro,True.intro⟩,True.intro⟩,⟨sg39110,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_643All : degreeTree62_643.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39089,degreeTree62_641All,degreeTree62_642All⟩

lemma degreeTree62_644All : degreeTree62_644.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39067,degreeTree62_640All,degreeTree62_643All⟩

lemma degreeTree62_645All : degreeTree62_645.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39122,⟨sg39117,⟨sg39114,⟨sg39113,⟨sg39112,True.intro,True.intro⟩,True.intro⟩,⟨sg39116,⟨sg39115,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39120,⟨sg39119,⟨sg39118,True.intro,True.intro⟩,True.intro⟩,⟨sg39121,True.intro,True.intro⟩⟩⟩,⟨sg39128,⟨sg39125,⟨sg39124,⟨sg39123,True.intro,True.intro⟩,True.intro⟩,⟨sg39127,⟨sg39126,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39131,⟨sg39130,⟨sg39129,True.intro,True.intro⟩,True.intro⟩,⟨sg39132,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_646All : degreeTree62_646.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39144,⟨sg39139,⟨sg39136,⟨sg39135,⟨sg39134,True.intro,True.intro⟩,True.intro⟩,⟨sg39138,⟨sg39137,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39142,⟨sg39141,⟨sg39140,True.intro,True.intro⟩,True.intro⟩,⟨sg39143,True.intro,True.intro⟩⟩⟩,⟨sg39150,⟨sg39147,⟨sg39146,⟨sg39145,True.intro,True.intro⟩,True.intro⟩,⟨sg39149,⟨sg39148,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39153,⟨sg39152,⟨sg39151,True.intro,True.intro⟩,True.intro⟩,⟨sg39154,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_647All : degreeTree62_647.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39133,degreeTree62_645All,degreeTree62_646All⟩

lemma degreeTree62_648All : degreeTree62_648.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39166,⟨sg39161,⟨sg39158,⟨sg39157,⟨sg39156,True.intro,True.intro⟩,True.intro⟩,⟨sg39160,⟨sg39159,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39164,⟨sg39163,⟨sg39162,True.intro,True.intro⟩,True.intro⟩,⟨sg39165,True.intro,True.intro⟩⟩⟩,⟨sg39172,⟨sg39169,⟨sg39168,⟨sg39167,True.intro,True.intro⟩,True.intro⟩,⟨sg39171,⟨sg39170,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39175,⟨sg39174,⟨sg39173,True.intro,True.intro⟩,True.intro⟩,⟨sg39176,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_649All : degreeTree62_649.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39188,⟨sg39183,⟨sg39180,⟨sg39179,⟨sg39178,True.intro,True.intro⟩,True.intro⟩,⟨sg39182,⟨sg39181,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39186,⟨sg39185,⟨sg39184,True.intro,True.intro⟩,True.intro⟩,⟨sg39187,True.intro,True.intro⟩⟩⟩,⟨sg39194,⟨sg39191,⟨sg39190,⟨sg39189,True.intro,True.intro⟩,True.intro⟩,⟨sg39193,⟨sg39192,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39197,⟨sg39196,⟨sg39195,True.intro,True.intro⟩,True.intro⟩,⟨sg39198,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_650All : degreeTree62_650.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39177,degreeTree62_648All,degreeTree62_649All⟩

lemma degreeTree62_651All : degreeTree62_651.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39155,degreeTree62_647All,degreeTree62_650All⟩

lemma degreeTree62_652All : degreeTree62_652.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39111,degreeTree62_644All,degreeTree62_651All⟩

lemma degreeTree62_653All : degreeTree62_653.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39210,⟨sg39205,⟨sg39202,⟨sg39201,⟨sg39200,True.intro,True.intro⟩,True.intro⟩,⟨sg39204,⟨sg39203,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39208,⟨sg39207,⟨sg39206,True.intro,True.intro⟩,True.intro⟩,⟨sg39209,True.intro,True.intro⟩⟩⟩,⟨sg39216,⟨sg39213,⟨sg39212,⟨sg39211,True.intro,True.intro⟩,True.intro⟩,⟨sg39215,⟨sg39214,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39219,⟨sg39218,⟨sg39217,True.intro,True.intro⟩,True.intro⟩,⟨sg39220,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_654All : degreeTree62_654.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39232,⟨sg39227,⟨sg39224,⟨sg39223,⟨sg39222,True.intro,True.intro⟩,True.intro⟩,⟨sg39226,⟨sg39225,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39230,⟨sg39229,⟨sg39228,True.intro,True.intro⟩,True.intro⟩,⟨sg39231,True.intro,True.intro⟩⟩⟩,⟨sg39238,⟨sg39235,⟨sg39234,⟨sg39233,True.intro,True.intro⟩,True.intro⟩,⟨sg39237,⟨sg39236,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39241,⟨sg39240,⟨sg39239,True.intro,True.intro⟩,True.intro⟩,⟨sg39242,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_655All : degreeTree62_655.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39221,degreeTree62_653All,degreeTree62_654All⟩

lemma degreeTree62_656All : degreeTree62_656.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39254,⟨sg39249,⟨sg39246,⟨sg39245,⟨sg39244,True.intro,True.intro⟩,True.intro⟩,⟨sg39248,⟨sg39247,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39252,⟨sg39251,⟨sg39250,True.intro,True.intro⟩,True.intro⟩,⟨sg39253,True.intro,True.intro⟩⟩⟩,⟨sg39260,⟨sg39257,⟨sg39256,⟨sg39255,True.intro,True.intro⟩,True.intro⟩,⟨sg39259,⟨sg39258,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39263,⟨sg39262,⟨sg39261,True.intro,True.intro⟩,True.intro⟩,⟨sg39264,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_657All : degreeTree62_657.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39276,⟨sg39271,⟨sg39268,⟨sg39267,⟨sg39266,True.intro,True.intro⟩,True.intro⟩,⟨sg39270,⟨sg39269,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39274,⟨sg39273,⟨sg39272,True.intro,True.intro⟩,True.intro⟩,⟨sg39275,True.intro,True.intro⟩⟩⟩,⟨sg39282,⟨sg39279,⟨sg39278,⟨sg39277,True.intro,True.intro⟩,True.intro⟩,⟨sg39281,⟨sg39280,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39285,⟨sg39284,⟨sg39283,True.intro,True.intro⟩,True.intro⟩,⟨sg39286,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_658All : degreeTree62_658.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39265,degreeTree62_656All,degreeTree62_657All⟩

lemma degreeTree62_659All : degreeTree62_659.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39243,degreeTree62_655All,degreeTree62_658All⟩

lemma degreeTree62_660All : degreeTree62_660.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39298,⟨sg39293,⟨sg39290,⟨sg39289,⟨sg39288,True.intro,True.intro⟩,True.intro⟩,⟨sg39292,⟨sg39291,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39296,⟨sg39295,⟨sg39294,True.intro,True.intro⟩,True.intro⟩,⟨sg39297,True.intro,True.intro⟩⟩⟩,⟨sg39304,⟨sg39301,⟨sg39300,⟨sg39299,True.intro,True.intro⟩,True.intro⟩,⟨sg39303,⟨sg39302,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39307,⟨sg39306,⟨sg39305,True.intro,True.intro⟩,True.intro⟩,⟨sg39308,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_661All : degreeTree62_661.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39320,⟨sg39315,⟨sg39312,⟨sg39311,⟨sg39310,True.intro,True.intro⟩,True.intro⟩,⟨sg39314,⟨sg39313,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39318,⟨sg39317,⟨sg39316,True.intro,True.intro⟩,True.intro⟩,⟨sg39319,True.intro,True.intro⟩⟩⟩,⟨sg39326,⟨sg39323,⟨sg39322,⟨sg39321,True.intro,True.intro⟩,True.intro⟩,⟨sg39325,⟨sg39324,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39329,⟨sg39328,⟨sg39327,True.intro,True.intro⟩,True.intro⟩,⟨sg39330,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_662All : degreeTree62_662.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39309,degreeTree62_660All,degreeTree62_661All⟩

lemma degreeTree62_663All : degreeTree62_663.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39342,⟨sg39337,⟨sg39334,⟨sg39333,⟨sg39332,True.intro,True.intro⟩,True.intro⟩,⟨sg39336,⟨sg39335,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39340,⟨sg39339,⟨sg39338,True.intro,True.intro⟩,True.intro⟩,⟨sg39341,True.intro,True.intro⟩⟩⟩,⟨sg39348,⟨sg39345,⟨sg39344,⟨sg39343,True.intro,True.intro⟩,True.intro⟩,⟨sg39347,⟨sg39346,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39351,⟨sg39350,⟨sg39349,True.intro,True.intro⟩,True.intro⟩,⟨sg39352,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_664All : degreeTree62_664.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39364,⟨sg39359,⟨sg39356,⟨sg39355,⟨sg39354,True.intro,True.intro⟩,True.intro⟩,⟨sg39358,⟨sg39357,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39362,⟨sg39361,⟨sg39360,True.intro,True.intro⟩,True.intro⟩,⟨sg39363,True.intro,True.intro⟩⟩⟩,⟨sg39369,⟨sg39367,⟨sg39366,⟨sg39365,True.intro,True.intro⟩,True.intro⟩,⟨sg39368,True.intro,True.intro⟩⟩,⟨sg39372,⟨sg39371,⟨sg39370,True.intro,True.intro⟩,True.intro⟩,⟨sg39373,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_665All : degreeTree62_665.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39353,degreeTree62_663All,degreeTree62_664All⟩

lemma degreeTree62_666All : degreeTree62_666.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39331,degreeTree62_662All,degreeTree62_665All⟩

lemma degreeTree62_667All : degreeTree62_667.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39287,degreeTree62_659All,degreeTree62_666All⟩

lemma degreeTree62_668All : degreeTree62_668.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39199,degreeTree62_652All,degreeTree62_667All⟩

lemma degreeTree62_669All : degreeTree62_669.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39385,⟨sg39380,⟨sg39377,⟨sg39376,⟨sg39375,True.intro,True.intro⟩,True.intro⟩,⟨sg39379,⟨sg39378,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39383,⟨sg39382,⟨sg39381,True.intro,True.intro⟩,True.intro⟩,⟨sg39384,True.intro,True.intro⟩⟩⟩,⟨sg39391,⟨sg39388,⟨sg39387,⟨sg39386,True.intro,True.intro⟩,True.intro⟩,⟨sg39390,⟨sg39389,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39394,⟨sg39393,⟨sg39392,True.intro,True.intro⟩,True.intro⟩,⟨sg39395,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_670All : degreeTree62_670.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39407,⟨sg39402,⟨sg39399,⟨sg39398,⟨sg39397,True.intro,True.intro⟩,True.intro⟩,⟨sg39401,⟨sg39400,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39405,⟨sg39404,⟨sg39403,True.intro,True.intro⟩,True.intro⟩,⟨sg39406,True.intro,True.intro⟩⟩⟩,⟨sg39413,⟨sg39410,⟨sg39409,⟨sg39408,True.intro,True.intro⟩,True.intro⟩,⟨sg39412,⟨sg39411,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39416,⟨sg39415,⟨sg39414,True.intro,True.intro⟩,True.intro⟩,⟨sg39417,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_671All : degreeTree62_671.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39396,degreeTree62_669All,degreeTree62_670All⟩

lemma degreeTree62_672All : degreeTree62_672.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39429,⟨sg39424,⟨sg39421,⟨sg39420,⟨sg39419,True.intro,True.intro⟩,True.intro⟩,⟨sg39423,⟨sg39422,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39427,⟨sg39426,⟨sg39425,True.intro,True.intro⟩,True.intro⟩,⟨sg39428,True.intro,True.intro⟩⟩⟩,⟨sg39435,⟨sg39432,⟨sg39431,⟨sg39430,True.intro,True.intro⟩,True.intro⟩,⟨sg39434,⟨sg39433,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39438,⟨sg39437,⟨sg39436,True.intro,True.intro⟩,True.intro⟩,⟨sg39439,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_673All : degreeTree62_673.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39451,⟨sg39446,⟨sg39443,⟨sg39442,⟨sg39441,True.intro,True.intro⟩,True.intro⟩,⟨sg39445,⟨sg39444,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39449,⟨sg39448,⟨sg39447,True.intro,True.intro⟩,True.intro⟩,⟨sg39450,True.intro,True.intro⟩⟩⟩,⟨sg39457,⟨sg39454,⟨sg39453,⟨sg39452,True.intro,True.intro⟩,True.intro⟩,⟨sg39456,⟨sg39455,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39460,⟨sg39459,⟨sg39458,True.intro,True.intro⟩,True.intro⟩,⟨sg39461,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_674All : degreeTree62_674.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39440,degreeTree62_672All,degreeTree62_673All⟩

lemma degreeTree62_675All : degreeTree62_675.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39418,degreeTree62_671All,degreeTree62_674All⟩

lemma degreeTree62_676All : degreeTree62_676.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39473,⟨sg39468,⟨sg39465,⟨sg39464,⟨sg39463,True.intro,True.intro⟩,True.intro⟩,⟨sg39467,⟨sg39466,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39471,⟨sg39470,⟨sg39469,True.intro,True.intro⟩,True.intro⟩,⟨sg39472,True.intro,True.intro⟩⟩⟩,⟨sg39479,⟨sg39476,⟨sg39475,⟨sg39474,True.intro,True.intro⟩,True.intro⟩,⟨sg39478,⟨sg39477,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39482,⟨sg39481,⟨sg39480,True.intro,True.intro⟩,True.intro⟩,⟨sg39483,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_677All : degreeTree62_677.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39495,⟨sg39490,⟨sg39487,⟨sg39486,⟨sg39485,True.intro,True.intro⟩,True.intro⟩,⟨sg39489,⟨sg39488,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39493,⟨sg39492,⟨sg39491,True.intro,True.intro⟩,True.intro⟩,⟨sg39494,True.intro,True.intro⟩⟩⟩,⟨sg39501,⟨sg39498,⟨sg39497,⟨sg39496,True.intro,True.intro⟩,True.intro⟩,⟨sg39500,⟨sg39499,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39504,⟨sg39503,⟨sg39502,True.intro,True.intro⟩,True.intro⟩,⟨sg39505,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_678All : degreeTree62_678.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39484,degreeTree62_676All,degreeTree62_677All⟩

lemma degreeTree62_679All : degreeTree62_679.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39517,⟨sg39512,⟨sg39509,⟨sg39508,⟨sg39507,True.intro,True.intro⟩,True.intro⟩,⟨sg39511,⟨sg39510,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39515,⟨sg39514,⟨sg39513,True.intro,True.intro⟩,True.intro⟩,⟨sg39516,True.intro,True.intro⟩⟩⟩,⟨sg39523,⟨sg39520,⟨sg39519,⟨sg39518,True.intro,True.intro⟩,True.intro⟩,⟨sg39522,⟨sg39521,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39526,⟨sg39525,⟨sg39524,True.intro,True.intro⟩,True.intro⟩,⟨sg39527,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_680All : degreeTree62_680.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39539,⟨sg39534,⟨sg39531,⟨sg39530,⟨sg39529,True.intro,True.intro⟩,True.intro⟩,⟨sg39533,⟨sg39532,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39537,⟨sg39536,⟨sg39535,True.intro,True.intro⟩,True.intro⟩,⟨sg39538,True.intro,True.intro⟩⟩⟩,⟨sg39545,⟨sg39542,⟨sg39541,⟨sg39540,True.intro,True.intro⟩,True.intro⟩,⟨sg39544,⟨sg39543,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39548,⟨sg39547,⟨sg39546,True.intro,True.intro⟩,True.intro⟩,⟨sg39549,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_681All : degreeTree62_681.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39528,degreeTree62_679All,degreeTree62_680All⟩

lemma degreeTree62_682All : degreeTree62_682.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39506,degreeTree62_678All,degreeTree62_681All⟩

lemma degreeTree62_683All : degreeTree62_683.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39462,degreeTree62_675All,degreeTree62_682All⟩

lemma degreeTree62_684All : degreeTree62_684.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39561,⟨sg39556,⟨sg39553,⟨sg39552,⟨sg39551,True.intro,True.intro⟩,True.intro⟩,⟨sg39555,⟨sg39554,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39559,⟨sg39558,⟨sg39557,True.intro,True.intro⟩,True.intro⟩,⟨sg39560,True.intro,True.intro⟩⟩⟩,⟨sg39567,⟨sg39564,⟨sg39563,⟨sg39562,True.intro,True.intro⟩,True.intro⟩,⟨sg39566,⟨sg39565,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39570,⟨sg39569,⟨sg39568,True.intro,True.intro⟩,True.intro⟩,⟨sg39571,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_685All : degreeTree62_685.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39583,⟨sg39578,⟨sg39575,⟨sg39574,⟨sg39573,True.intro,True.intro⟩,True.intro⟩,⟨sg39577,⟨sg39576,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39581,⟨sg39580,⟨sg39579,True.intro,True.intro⟩,True.intro⟩,⟨sg39582,True.intro,True.intro⟩⟩⟩,⟨sg39589,⟨sg39586,⟨sg39585,⟨sg39584,True.intro,True.intro⟩,True.intro⟩,⟨sg39588,⟨sg39587,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39592,⟨sg39591,⟨sg39590,True.intro,True.intro⟩,True.intro⟩,⟨sg39593,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_686All : degreeTree62_686.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39572,degreeTree62_684All,degreeTree62_685All⟩

lemma degreeTree62_687All : degreeTree62_687.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39605,⟨sg39600,⟨sg39597,⟨sg39596,⟨sg39595,True.intro,True.intro⟩,True.intro⟩,⟨sg39599,⟨sg39598,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39603,⟨sg39602,⟨sg39601,True.intro,True.intro⟩,True.intro⟩,⟨sg39604,True.intro,True.intro⟩⟩⟩,⟨sg39611,⟨sg39608,⟨sg39607,⟨sg39606,True.intro,True.intro⟩,True.intro⟩,⟨sg39610,⟨sg39609,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39614,⟨sg39613,⟨sg39612,True.intro,True.intro⟩,True.intro⟩,⟨sg39615,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_688All : degreeTree62_688.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39627,⟨sg39622,⟨sg39619,⟨sg39618,⟨sg39617,True.intro,True.intro⟩,True.intro⟩,⟨sg39621,⟨sg39620,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39625,⟨sg39624,⟨sg39623,True.intro,True.intro⟩,True.intro⟩,⟨sg39626,True.intro,True.intro⟩⟩⟩,⟨sg39633,⟨sg39630,⟨sg39629,⟨sg39628,True.intro,True.intro⟩,True.intro⟩,⟨sg39632,⟨sg39631,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39636,⟨sg39635,⟨sg39634,True.intro,True.intro⟩,True.intro⟩,⟨sg39637,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_689All : degreeTree62_689.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39616,degreeTree62_687All,degreeTree62_688All⟩

lemma degreeTree62_690All : degreeTree62_690.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39594,degreeTree62_686All,degreeTree62_689All⟩

lemma degreeTree62_691All : degreeTree62_691.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39649,⟨sg39644,⟨sg39641,⟨sg39640,⟨sg39639,True.intro,True.intro⟩,True.intro⟩,⟨sg39643,⟨sg39642,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39647,⟨sg39646,⟨sg39645,True.intro,True.intro⟩,True.intro⟩,⟨sg39648,True.intro,True.intro⟩⟩⟩,⟨sg39655,⟨sg39652,⟨sg39651,⟨sg39650,True.intro,True.intro⟩,True.intro⟩,⟨sg39654,⟨sg39653,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39658,⟨sg39657,⟨sg39656,True.intro,True.intro⟩,True.intro⟩,⟨sg39659,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_692All : degreeTree62_692.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39671,⟨sg39666,⟨sg39663,⟨sg39662,⟨sg39661,True.intro,True.intro⟩,True.intro⟩,⟨sg39665,⟨sg39664,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39669,⟨sg39668,⟨sg39667,True.intro,True.intro⟩,True.intro⟩,⟨sg39670,True.intro,True.intro⟩⟩⟩,⟨sg39677,⟨sg39674,⟨sg39673,⟨sg39672,True.intro,True.intro⟩,True.intro⟩,⟨sg39676,⟨sg39675,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39680,⟨sg39679,⟨sg39678,True.intro,True.intro⟩,True.intro⟩,⟨sg39681,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_693All : degreeTree62_693.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39660,degreeTree62_691All,degreeTree62_692All⟩

lemma degreeTree62_694All : degreeTree62_694.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39693,⟨sg39688,⟨sg39685,⟨sg39684,⟨sg39683,True.intro,True.intro⟩,True.intro⟩,⟨sg39687,⟨sg39686,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39691,⟨sg39690,⟨sg39689,True.intro,True.intro⟩,True.intro⟩,⟨sg39692,True.intro,True.intro⟩⟩⟩,⟨sg39699,⟨sg39696,⟨sg39695,⟨sg39694,True.intro,True.intro⟩,True.intro⟩,⟨sg39698,⟨sg39697,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39702,⟨sg39701,⟨sg39700,True.intro,True.intro⟩,True.intro⟩,⟨sg39703,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_695All : degreeTree62_695.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39715,⟨sg39710,⟨sg39707,⟨sg39706,⟨sg39705,True.intro,True.intro⟩,True.intro⟩,⟨sg39709,⟨sg39708,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39713,⟨sg39712,⟨sg39711,True.intro,True.intro⟩,True.intro⟩,⟨sg39714,True.intro,True.intro⟩⟩⟩,⟨sg39720,⟨sg39718,⟨sg39717,⟨sg39716,True.intro,True.intro⟩,True.intro⟩,⟨sg39719,True.intro,True.intro⟩⟩,⟨sg39723,⟨sg39722,⟨sg39721,True.intro,True.intro⟩,True.intro⟩,⟨sg39724,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_696All : degreeTree62_696.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39704,degreeTree62_694All,degreeTree62_695All⟩

lemma degreeTree62_697All : degreeTree62_697.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39682,degreeTree62_693All,degreeTree62_696All⟩

lemma degreeTree62_698All : degreeTree62_698.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39638,degreeTree62_690All,degreeTree62_697All⟩

lemma degreeTree62_699All : degreeTree62_699.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39550,degreeTree62_683All,degreeTree62_698All⟩

lemma degreeTree62_700All : degreeTree62_700.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39374,degreeTree62_668All,degreeTree62_699All⟩

lemma degreeTree62_701All : degreeTree62_701.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39736,⟨sg39731,⟨sg39728,⟨sg39727,⟨sg39726,True.intro,True.intro⟩,True.intro⟩,⟨sg39730,⟨sg39729,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39734,⟨sg39733,⟨sg39732,True.intro,True.intro⟩,True.intro⟩,⟨sg39735,True.intro,True.intro⟩⟩⟩,⟨sg39742,⟨sg39739,⟨sg39738,⟨sg39737,True.intro,True.intro⟩,True.intro⟩,⟨sg39741,⟨sg39740,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39745,⟨sg39744,⟨sg39743,True.intro,True.intro⟩,True.intro⟩,⟨sg39746,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_702All : degreeTree62_702.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39758,⟨sg39753,⟨sg39750,⟨sg39749,⟨sg39748,True.intro,True.intro⟩,True.intro⟩,⟨sg39752,⟨sg39751,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39756,⟨sg39755,⟨sg39754,True.intro,True.intro⟩,True.intro⟩,⟨sg39757,True.intro,True.intro⟩⟩⟩,⟨sg39764,⟨sg39761,⟨sg39760,⟨sg39759,True.intro,True.intro⟩,True.intro⟩,⟨sg39763,⟨sg39762,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39767,⟨sg39766,⟨sg39765,True.intro,True.intro⟩,True.intro⟩,⟨sg39768,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_703All : degreeTree62_703.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39747,degreeTree62_701All,degreeTree62_702All⟩

lemma degreeTree62_704All : degreeTree62_704.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39780,⟨sg39775,⟨sg39772,⟨sg39771,⟨sg39770,True.intro,True.intro⟩,True.intro⟩,⟨sg39774,⟨sg39773,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39778,⟨sg39777,⟨sg39776,True.intro,True.intro⟩,True.intro⟩,⟨sg39779,True.intro,True.intro⟩⟩⟩,⟨sg39786,⟨sg39783,⟨sg39782,⟨sg39781,True.intro,True.intro⟩,True.intro⟩,⟨sg39785,⟨sg39784,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39789,⟨sg39788,⟨sg39787,True.intro,True.intro⟩,True.intro⟩,⟨sg39790,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_705All : degreeTree62_705.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39802,⟨sg39797,⟨sg39794,⟨sg39793,⟨sg39792,True.intro,True.intro⟩,True.intro⟩,⟨sg39796,⟨sg39795,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39800,⟨sg39799,⟨sg39798,True.intro,True.intro⟩,True.intro⟩,⟨sg39801,True.intro,True.intro⟩⟩⟩,⟨sg39808,⟨sg39805,⟨sg39804,⟨sg39803,True.intro,True.intro⟩,True.intro⟩,⟨sg39807,⟨sg39806,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39811,⟨sg39810,⟨sg39809,True.intro,True.intro⟩,True.intro⟩,⟨sg39812,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_706All : degreeTree62_706.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39791,degreeTree62_704All,degreeTree62_705All⟩

lemma degreeTree62_707All : degreeTree62_707.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39769,degreeTree62_703All,degreeTree62_706All⟩

lemma degreeTree62_708All : degreeTree62_708.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39824,⟨sg39819,⟨sg39816,⟨sg39815,⟨sg39814,True.intro,True.intro⟩,True.intro⟩,⟨sg39818,⟨sg39817,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39822,⟨sg39821,⟨sg39820,True.intro,True.intro⟩,True.intro⟩,⟨sg39823,True.intro,True.intro⟩⟩⟩,⟨sg39830,⟨sg39827,⟨sg39826,⟨sg39825,True.intro,True.intro⟩,True.intro⟩,⟨sg39829,⟨sg39828,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39833,⟨sg39832,⟨sg39831,True.intro,True.intro⟩,True.intro⟩,⟨sg39834,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_709All : degreeTree62_709.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39846,⟨sg39841,⟨sg39838,⟨sg39837,⟨sg39836,True.intro,True.intro⟩,True.intro⟩,⟨sg39840,⟨sg39839,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39844,⟨sg39843,⟨sg39842,True.intro,True.intro⟩,True.intro⟩,⟨sg39845,True.intro,True.intro⟩⟩⟩,⟨sg39852,⟨sg39849,⟨sg39848,⟨sg39847,True.intro,True.intro⟩,True.intro⟩,⟨sg39851,⟨sg39850,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39855,⟨sg39854,⟨sg39853,True.intro,True.intro⟩,True.intro⟩,⟨sg39856,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_710All : degreeTree62_710.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39835,degreeTree62_708All,degreeTree62_709All⟩

lemma degreeTree62_711All : degreeTree62_711.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39868,⟨sg39863,⟨sg39860,⟨sg39859,⟨sg39858,True.intro,True.intro⟩,True.intro⟩,⟨sg39862,⟨sg39861,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39866,⟨sg39865,⟨sg39864,True.intro,True.intro⟩,True.intro⟩,⟨sg39867,True.intro,True.intro⟩⟩⟩,⟨sg39874,⟨sg39871,⟨sg39870,⟨sg39869,True.intro,True.intro⟩,True.intro⟩,⟨sg39873,⟨sg39872,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39877,⟨sg39876,⟨sg39875,True.intro,True.intro⟩,True.intro⟩,⟨sg39878,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_712All : degreeTree62_712.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39890,⟨sg39885,⟨sg39882,⟨sg39881,⟨sg39880,True.intro,True.intro⟩,True.intro⟩,⟨sg39884,⟨sg39883,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39888,⟨sg39887,⟨sg39886,True.intro,True.intro⟩,True.intro⟩,⟨sg39889,True.intro,True.intro⟩⟩⟩,⟨sg39896,⟨sg39893,⟨sg39892,⟨sg39891,True.intro,True.intro⟩,True.intro⟩,⟨sg39895,⟨sg39894,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39899,⟨sg39898,⟨sg39897,True.intro,True.intro⟩,True.intro⟩,⟨sg39900,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_713All : degreeTree62_713.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39879,degreeTree62_711All,degreeTree62_712All⟩

lemma degreeTree62_714All : degreeTree62_714.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39857,degreeTree62_710All,degreeTree62_713All⟩

lemma degreeTree62_715All : degreeTree62_715.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39813,degreeTree62_707All,degreeTree62_714All⟩

lemma degreeTree62_716All : degreeTree62_716.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39912,⟨sg39907,⟨sg39904,⟨sg39903,⟨sg39902,True.intro,True.intro⟩,True.intro⟩,⟨sg39906,⟨sg39905,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39910,⟨sg39909,⟨sg39908,True.intro,True.intro⟩,True.intro⟩,⟨sg39911,True.intro,True.intro⟩⟩⟩,⟨sg39918,⟨sg39915,⟨sg39914,⟨sg39913,True.intro,True.intro⟩,True.intro⟩,⟨sg39917,⟨sg39916,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39921,⟨sg39920,⟨sg39919,True.intro,True.intro⟩,True.intro⟩,⟨sg39922,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_717All : degreeTree62_717.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39934,⟨sg39929,⟨sg39926,⟨sg39925,⟨sg39924,True.intro,True.intro⟩,True.intro⟩,⟨sg39928,⟨sg39927,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39932,⟨sg39931,⟨sg39930,True.intro,True.intro⟩,True.intro⟩,⟨sg39933,True.intro,True.intro⟩⟩⟩,⟨sg39940,⟨sg39937,⟨sg39936,⟨sg39935,True.intro,True.intro⟩,True.intro⟩,⟨sg39939,⟨sg39938,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39943,⟨sg39942,⟨sg39941,True.intro,True.intro⟩,True.intro⟩,⟨sg39944,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_718All : degreeTree62_718.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39923,degreeTree62_716All,degreeTree62_717All⟩

lemma degreeTree62_719All : degreeTree62_719.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39956,⟨sg39951,⟨sg39948,⟨sg39947,⟨sg39946,True.intro,True.intro⟩,True.intro⟩,⟨sg39950,⟨sg39949,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39954,⟨sg39953,⟨sg39952,True.intro,True.intro⟩,True.intro⟩,⟨sg39955,True.intro,True.intro⟩⟩⟩,⟨sg39962,⟨sg39959,⟨sg39958,⟨sg39957,True.intro,True.intro⟩,True.intro⟩,⟨sg39961,⟨sg39960,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39965,⟨sg39964,⟨sg39963,True.intro,True.intro⟩,True.intro⟩,⟨sg39966,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_720All : degreeTree62_720.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39978,⟨sg39973,⟨sg39970,⟨sg39969,⟨sg39968,True.intro,True.intro⟩,True.intro⟩,⟨sg39972,⟨sg39971,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39976,⟨sg39975,⟨sg39974,True.intro,True.intro⟩,True.intro⟩,⟨sg39977,True.intro,True.intro⟩⟩⟩,⟨sg39984,⟨sg39981,⟨sg39980,⟨sg39979,True.intro,True.intro⟩,True.intro⟩,⟨sg39983,⟨sg39982,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39987,⟨sg39986,⟨sg39985,True.intro,True.intro⟩,True.intro⟩,⟨sg39988,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_721All : degreeTree62_721.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39967,degreeTree62_719All,degreeTree62_720All⟩

lemma degreeTree62_722All : degreeTree62_722.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39945,degreeTree62_718All,degreeTree62_721All⟩

lemma degreeTree62_723All : degreeTree62_723.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40000,⟨sg39995,⟨sg39992,⟨sg39991,⟨sg39990,True.intro,True.intro⟩,True.intro⟩,⟨sg39994,⟨sg39993,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg39998,⟨sg39997,⟨sg39996,True.intro,True.intro⟩,True.intro⟩,⟨sg39999,True.intro,True.intro⟩⟩⟩,⟨sg40006,⟨sg40003,⟨sg40002,⟨sg40001,True.intro,True.intro⟩,True.intro⟩,⟨sg40005,⟨sg40004,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40009,⟨sg40008,⟨sg40007,True.intro,True.intro⟩,True.intro⟩,⟨sg40010,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_724All : degreeTree62_724.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40022,⟨sg40017,⟨sg40014,⟨sg40013,⟨sg40012,True.intro,True.intro⟩,True.intro⟩,⟨sg40016,⟨sg40015,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40020,⟨sg40019,⟨sg40018,True.intro,True.intro⟩,True.intro⟩,⟨sg40021,True.intro,True.intro⟩⟩⟩,⟨sg40028,⟨sg40025,⟨sg40024,⟨sg40023,True.intro,True.intro⟩,True.intro⟩,⟨sg40027,⟨sg40026,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40031,⟨sg40030,⟨sg40029,True.intro,True.intro⟩,True.intro⟩,⟨sg40032,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_725All : degreeTree62_725.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40011,degreeTree62_723All,degreeTree62_724All⟩

lemma degreeTree62_726All : degreeTree62_726.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40044,⟨sg40039,⟨sg40036,⟨sg40035,⟨sg40034,True.intro,True.intro⟩,True.intro⟩,⟨sg40038,⟨sg40037,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40042,⟨sg40041,⟨sg40040,True.intro,True.intro⟩,True.intro⟩,⟨sg40043,True.intro,True.intro⟩⟩⟩,⟨sg40050,⟨sg40047,⟨sg40046,⟨sg40045,True.intro,True.intro⟩,True.intro⟩,⟨sg40049,⟨sg40048,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40053,⟨sg40052,⟨sg40051,True.intro,True.intro⟩,True.intro⟩,⟨sg40054,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_727All : degreeTree62_727.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40066,⟨sg40061,⟨sg40058,⟨sg40057,⟨sg40056,True.intro,True.intro⟩,True.intro⟩,⟨sg40060,⟨sg40059,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40064,⟨sg40063,⟨sg40062,True.intro,True.intro⟩,True.intro⟩,⟨sg40065,True.intro,True.intro⟩⟩⟩,⟨sg40071,⟨sg40069,⟨sg40068,⟨sg40067,True.intro,True.intro⟩,True.intro⟩,⟨sg40070,True.intro,True.intro⟩⟩,⟨sg40074,⟨sg40073,⟨sg40072,True.intro,True.intro⟩,True.intro⟩,⟨sg40075,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_728All : degreeTree62_728.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40055,degreeTree62_726All,degreeTree62_727All⟩

lemma degreeTree62_729All : degreeTree62_729.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40033,degreeTree62_725All,degreeTree62_728All⟩

lemma degreeTree62_730All : degreeTree62_730.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39989,degreeTree62_722All,degreeTree62_729All⟩

lemma degreeTree62_731All : degreeTree62_731.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39901,degreeTree62_715All,degreeTree62_730All⟩

lemma degreeTree62_732All : degreeTree62_732.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40087,⟨sg40082,⟨sg40079,⟨sg40078,⟨sg40077,True.intro,True.intro⟩,True.intro⟩,⟨sg40081,⟨sg40080,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40085,⟨sg40084,⟨sg40083,True.intro,True.intro⟩,True.intro⟩,⟨sg40086,True.intro,True.intro⟩⟩⟩,⟨sg40093,⟨sg40090,⟨sg40089,⟨sg40088,True.intro,True.intro⟩,True.intro⟩,⟨sg40092,⟨sg40091,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40096,⟨sg40095,⟨sg40094,True.intro,True.intro⟩,True.intro⟩,⟨sg40097,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_733All : degreeTree62_733.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40109,⟨sg40104,⟨sg40101,⟨sg40100,⟨sg40099,True.intro,True.intro⟩,True.intro⟩,⟨sg40103,⟨sg40102,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40107,⟨sg40106,⟨sg40105,True.intro,True.intro⟩,True.intro⟩,⟨sg40108,True.intro,True.intro⟩⟩⟩,⟨sg40115,⟨sg40112,⟨sg40111,⟨sg40110,True.intro,True.intro⟩,True.intro⟩,⟨sg40114,⟨sg40113,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40118,⟨sg40117,⟨sg40116,True.intro,True.intro⟩,True.intro⟩,⟨sg40119,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_734All : degreeTree62_734.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40098,degreeTree62_732All,degreeTree62_733All⟩

lemma degreeTree62_735All : degreeTree62_735.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40131,⟨sg40126,⟨sg40123,⟨sg40122,⟨sg40121,True.intro,True.intro⟩,True.intro⟩,⟨sg40125,⟨sg40124,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40129,⟨sg40128,⟨sg40127,True.intro,True.intro⟩,True.intro⟩,⟨sg40130,True.intro,True.intro⟩⟩⟩,⟨sg40137,⟨sg40134,⟨sg40133,⟨sg40132,True.intro,True.intro⟩,True.intro⟩,⟨sg40136,⟨sg40135,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40140,⟨sg40139,⟨sg40138,True.intro,True.intro⟩,True.intro⟩,⟨sg40141,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_736All : degreeTree62_736.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40153,⟨sg40148,⟨sg40145,⟨sg40144,⟨sg40143,True.intro,True.intro⟩,True.intro⟩,⟨sg40147,⟨sg40146,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40151,⟨sg40150,⟨sg40149,True.intro,True.intro⟩,True.intro⟩,⟨sg40152,True.intro,True.intro⟩⟩⟩,⟨sg40159,⟨sg40156,⟨sg40155,⟨sg40154,True.intro,True.intro⟩,True.intro⟩,⟨sg40158,⟨sg40157,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40162,⟨sg40161,⟨sg40160,True.intro,True.intro⟩,True.intro⟩,⟨sg40163,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_737All : degreeTree62_737.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40142,degreeTree62_735All,degreeTree62_736All⟩

lemma degreeTree62_738All : degreeTree62_738.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40120,degreeTree62_734All,degreeTree62_737All⟩

lemma degreeTree62_739All : degreeTree62_739.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40175,⟨sg40170,⟨sg40167,⟨sg40166,⟨sg40165,True.intro,True.intro⟩,True.intro⟩,⟨sg40169,⟨sg40168,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40173,⟨sg40172,⟨sg40171,True.intro,True.intro⟩,True.intro⟩,⟨sg40174,True.intro,True.intro⟩⟩⟩,⟨sg40181,⟨sg40178,⟨sg40177,⟨sg40176,True.intro,True.intro⟩,True.intro⟩,⟨sg40180,⟨sg40179,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40184,⟨sg40183,⟨sg40182,True.intro,True.intro⟩,True.intro⟩,⟨sg40185,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_740All : degreeTree62_740.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40197,⟨sg40192,⟨sg40189,⟨sg40188,⟨sg40187,True.intro,True.intro⟩,True.intro⟩,⟨sg40191,⟨sg40190,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40195,⟨sg40194,⟨sg40193,True.intro,True.intro⟩,True.intro⟩,⟨sg40196,True.intro,True.intro⟩⟩⟩,⟨sg40203,⟨sg40200,⟨sg40199,⟨sg40198,True.intro,True.intro⟩,True.intro⟩,⟨sg40202,⟨sg40201,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40206,⟨sg40205,⟨sg40204,True.intro,True.intro⟩,True.intro⟩,⟨sg40207,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_741All : degreeTree62_741.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40186,degreeTree62_739All,degreeTree62_740All⟩

lemma degreeTree62_742All : degreeTree62_742.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40219,⟨sg40214,⟨sg40211,⟨sg40210,⟨sg40209,True.intro,True.intro⟩,True.intro⟩,⟨sg40213,⟨sg40212,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40217,⟨sg40216,⟨sg40215,True.intro,True.intro⟩,True.intro⟩,⟨sg40218,True.intro,True.intro⟩⟩⟩,⟨sg40225,⟨sg40222,⟨sg40221,⟨sg40220,True.intro,True.intro⟩,True.intro⟩,⟨sg40224,⟨sg40223,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40228,⟨sg40227,⟨sg40226,True.intro,True.intro⟩,True.intro⟩,⟨sg40229,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_743All : degreeTree62_743.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40241,⟨sg40236,⟨sg40233,⟨sg40232,⟨sg40231,True.intro,True.intro⟩,True.intro⟩,⟨sg40235,⟨sg40234,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40239,⟨sg40238,⟨sg40237,True.intro,True.intro⟩,True.intro⟩,⟨sg40240,True.intro,True.intro⟩⟩⟩,⟨sg40246,⟨sg40244,⟨sg40243,⟨sg40242,True.intro,True.intro⟩,True.intro⟩,⟨sg40245,True.intro,True.intro⟩⟩,⟨sg40249,⟨sg40248,⟨sg40247,True.intro,True.intro⟩,True.intro⟩,⟨sg40250,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_744All : degreeTree62_744.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40230,degreeTree62_742All,degreeTree62_743All⟩

lemma degreeTree62_745All : degreeTree62_745.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40208,degreeTree62_741All,degreeTree62_744All⟩

lemma degreeTree62_746All : degreeTree62_746.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40164,degreeTree62_738All,degreeTree62_745All⟩

lemma degreeTree62_747All : degreeTree62_747.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40262,⟨sg40257,⟨sg40254,⟨sg40253,⟨sg40252,True.intro,True.intro⟩,True.intro⟩,⟨sg40256,⟨sg40255,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40260,⟨sg40259,⟨sg40258,True.intro,True.intro⟩,True.intro⟩,⟨sg40261,True.intro,True.intro⟩⟩⟩,⟨sg40268,⟨sg40265,⟨sg40264,⟨sg40263,True.intro,True.intro⟩,True.intro⟩,⟨sg40267,⟨sg40266,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40271,⟨sg40270,⟨sg40269,True.intro,True.intro⟩,True.intro⟩,⟨sg40272,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_748All : degreeTree62_748.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40284,⟨sg40279,⟨sg40276,⟨sg40275,⟨sg40274,True.intro,True.intro⟩,True.intro⟩,⟨sg40278,⟨sg40277,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40282,⟨sg40281,⟨sg40280,True.intro,True.intro⟩,True.intro⟩,⟨sg40283,True.intro,True.intro⟩⟩⟩,⟨sg40290,⟨sg40287,⟨sg40286,⟨sg40285,True.intro,True.intro⟩,True.intro⟩,⟨sg40289,⟨sg40288,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40293,⟨sg40292,⟨sg40291,True.intro,True.intro⟩,True.intro⟩,⟨sg40294,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_749All : degreeTree62_749.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40273,degreeTree62_747All,degreeTree62_748All⟩

lemma degreeTree62_750All : degreeTree62_750.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40306,⟨sg40301,⟨sg40298,⟨sg40297,⟨sg40296,True.intro,True.intro⟩,True.intro⟩,⟨sg40300,⟨sg40299,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40304,⟨sg40303,⟨sg40302,True.intro,True.intro⟩,True.intro⟩,⟨sg40305,True.intro,True.intro⟩⟩⟩,⟨sg40312,⟨sg40309,⟨sg40308,⟨sg40307,True.intro,True.intro⟩,True.intro⟩,⟨sg40311,⟨sg40310,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40315,⟨sg40314,⟨sg40313,True.intro,True.intro⟩,True.intro⟩,⟨sg40316,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_751All : degreeTree62_751.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40328,⟨sg40323,⟨sg40320,⟨sg40319,⟨sg40318,True.intro,True.intro⟩,True.intro⟩,⟨sg40322,⟨sg40321,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40326,⟨sg40325,⟨sg40324,True.intro,True.intro⟩,True.intro⟩,⟨sg40327,True.intro,True.intro⟩⟩⟩,⟨sg40334,⟨sg40331,⟨sg40330,⟨sg40329,True.intro,True.intro⟩,True.intro⟩,⟨sg40333,⟨sg40332,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40337,⟨sg40336,⟨sg40335,True.intro,True.intro⟩,True.intro⟩,⟨sg40338,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_752All : degreeTree62_752.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40317,degreeTree62_750All,degreeTree62_751All⟩

lemma degreeTree62_753All : degreeTree62_753.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40295,degreeTree62_749All,degreeTree62_752All⟩

lemma degreeTree62_754All : degreeTree62_754.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40350,⟨sg40345,⟨sg40342,⟨sg40341,⟨sg40340,True.intro,True.intro⟩,True.intro⟩,⟨sg40344,⟨sg40343,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40348,⟨sg40347,⟨sg40346,True.intro,True.intro⟩,True.intro⟩,⟨sg40349,True.intro,True.intro⟩⟩⟩,⟨sg40356,⟨sg40353,⟨sg40352,⟨sg40351,True.intro,True.intro⟩,True.intro⟩,⟨sg40355,⟨sg40354,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40359,⟨sg40358,⟨sg40357,True.intro,True.intro⟩,True.intro⟩,⟨sg40360,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_755All : degreeTree62_755.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40372,⟨sg40367,⟨sg40364,⟨sg40363,⟨sg40362,True.intro,True.intro⟩,True.intro⟩,⟨sg40366,⟨sg40365,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40370,⟨sg40369,⟨sg40368,True.intro,True.intro⟩,True.intro⟩,⟨sg40371,True.intro,True.intro⟩⟩⟩,⟨sg40378,⟨sg40375,⟨sg40374,⟨sg40373,True.intro,True.intro⟩,True.intro⟩,⟨sg40377,⟨sg40376,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40381,⟨sg40380,⟨sg40379,True.intro,True.intro⟩,True.intro⟩,⟨sg40382,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_756All : degreeTree62_756.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40361,degreeTree62_754All,degreeTree62_755All⟩

lemma degreeTree62_757All : degreeTree62_757.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40394,⟨sg40389,⟨sg40386,⟨sg40385,⟨sg40384,True.intro,True.intro⟩,True.intro⟩,⟨sg40388,⟨sg40387,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40392,⟨sg40391,⟨sg40390,True.intro,True.intro⟩,True.intro⟩,⟨sg40393,True.intro,True.intro⟩⟩⟩,⟨sg40400,⟨sg40397,⟨sg40396,⟨sg40395,True.intro,True.intro⟩,True.intro⟩,⟨sg40399,⟨sg40398,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40403,⟨sg40402,⟨sg40401,True.intro,True.intro⟩,True.intro⟩,⟨sg40404,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_758All : degreeTree62_758.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40416,⟨sg40411,⟨sg40408,⟨sg40407,⟨sg40406,True.intro,True.intro⟩,True.intro⟩,⟨sg40410,⟨sg40409,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40414,⟨sg40413,⟨sg40412,True.intro,True.intro⟩,True.intro⟩,⟨sg40415,True.intro,True.intro⟩⟩⟩,⟨sg40421,⟨sg40419,⟨sg40418,⟨sg40417,True.intro,True.intro⟩,True.intro⟩,⟨sg40420,True.intro,True.intro⟩⟩,⟨sg40424,⟨sg40423,⟨sg40422,True.intro,True.intro⟩,True.intro⟩,⟨sg40425,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_759All : degreeTree62_759.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40405,degreeTree62_757All,degreeTree62_758All⟩

lemma degreeTree62_760All : degreeTree62_760.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40383,degreeTree62_756All,degreeTree62_759All⟩

lemma degreeTree62_761All : degreeTree62_761.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40339,degreeTree62_753All,degreeTree62_760All⟩

lemma degreeTree62_762All : degreeTree62_762.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40251,degreeTree62_746All,degreeTree62_761All⟩

lemma degreeTree62_763All : degreeTree62_763.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40076,degreeTree62_731All,degreeTree62_762All⟩

lemma degreeTree62_764All : degreeTree62_764.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39725,degreeTree62_700All,degreeTree62_763All⟩

lemma degreeTree62_765All : degreeTree62_765.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg39023,degreeTree62_637All,degreeTree62_764All⟩

lemma degreeTree62_766All : degreeTree62_766.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40437,⟨sg40432,⟨sg40429,⟨sg40428,⟨sg40427,True.intro,True.intro⟩,True.intro⟩,⟨sg40431,⟨sg40430,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40435,⟨sg40434,⟨sg40433,True.intro,True.intro⟩,True.intro⟩,⟨sg40436,True.intro,True.intro⟩⟩⟩,⟨sg40443,⟨sg40440,⟨sg40439,⟨sg40438,True.intro,True.intro⟩,True.intro⟩,⟨sg40442,⟨sg40441,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40446,⟨sg40445,⟨sg40444,True.intro,True.intro⟩,True.intro⟩,⟨sg40447,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_767All : degreeTree62_767.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40459,⟨sg40454,⟨sg40451,⟨sg40450,⟨sg40449,True.intro,True.intro⟩,True.intro⟩,⟨sg40453,⟨sg40452,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40457,⟨sg40456,⟨sg40455,True.intro,True.intro⟩,True.intro⟩,⟨sg40458,True.intro,True.intro⟩⟩⟩,⟨sg40465,⟨sg40462,⟨sg40461,⟨sg40460,True.intro,True.intro⟩,True.intro⟩,⟨sg40464,⟨sg40463,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40468,⟨sg40467,⟨sg40466,True.intro,True.intro⟩,True.intro⟩,⟨sg40469,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_768All : degreeTree62_768.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40448,degreeTree62_766All,degreeTree62_767All⟩

lemma degreeTree62_769All : degreeTree62_769.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40481,⟨sg40476,⟨sg40473,⟨sg40472,⟨sg40471,True.intro,True.intro⟩,True.intro⟩,⟨sg40475,⟨sg40474,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40479,⟨sg40478,⟨sg40477,True.intro,True.intro⟩,True.intro⟩,⟨sg40480,True.intro,True.intro⟩⟩⟩,⟨sg40487,⟨sg40484,⟨sg40483,⟨sg40482,True.intro,True.intro⟩,True.intro⟩,⟨sg40486,⟨sg40485,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40490,⟨sg40489,⟨sg40488,True.intro,True.intro⟩,True.intro⟩,⟨sg40491,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_770All : degreeTree62_770.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40503,⟨sg40498,⟨sg40495,⟨sg40494,⟨sg40493,True.intro,True.intro⟩,True.intro⟩,⟨sg40497,⟨sg40496,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40501,⟨sg40500,⟨sg40499,True.intro,True.intro⟩,True.intro⟩,⟨sg40502,True.intro,True.intro⟩⟩⟩,⟨sg40509,⟨sg40506,⟨sg40505,⟨sg40504,True.intro,True.intro⟩,True.intro⟩,⟨sg40508,⟨sg40507,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40512,⟨sg40511,⟨sg40510,True.intro,True.intro⟩,True.intro⟩,⟨sg40513,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_771All : degreeTree62_771.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40492,degreeTree62_769All,degreeTree62_770All⟩

lemma degreeTree62_772All : degreeTree62_772.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40470,degreeTree62_768All,degreeTree62_771All⟩

lemma degreeTree62_773All : degreeTree62_773.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40525,⟨sg40520,⟨sg40517,⟨sg40516,⟨sg40515,True.intro,True.intro⟩,True.intro⟩,⟨sg40519,⟨sg40518,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40523,⟨sg40522,⟨sg40521,True.intro,True.intro⟩,True.intro⟩,⟨sg40524,True.intro,True.intro⟩⟩⟩,⟨sg40531,⟨sg40528,⟨sg40527,⟨sg40526,True.intro,True.intro⟩,True.intro⟩,⟨sg40530,⟨sg40529,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40534,⟨sg40533,⟨sg40532,True.intro,True.intro⟩,True.intro⟩,⟨sg40535,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_774All : degreeTree62_774.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40547,⟨sg40542,⟨sg40539,⟨sg40538,⟨sg40537,True.intro,True.intro⟩,True.intro⟩,⟨sg40541,⟨sg40540,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40545,⟨sg40544,⟨sg40543,True.intro,True.intro⟩,True.intro⟩,⟨sg40546,True.intro,True.intro⟩⟩⟩,⟨sg40553,⟨sg40550,⟨sg40549,⟨sg40548,True.intro,True.intro⟩,True.intro⟩,⟨sg40552,⟨sg40551,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40556,⟨sg40555,⟨sg40554,True.intro,True.intro⟩,True.intro⟩,⟨sg40557,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_775All : degreeTree62_775.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40536,degreeTree62_773All,degreeTree62_774All⟩

lemma degreeTree62_776All : degreeTree62_776.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40569,⟨sg40564,⟨sg40561,⟨sg40560,⟨sg40559,True.intro,True.intro⟩,True.intro⟩,⟨sg40563,⟨sg40562,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40567,⟨sg40566,⟨sg40565,True.intro,True.intro⟩,True.intro⟩,⟨sg40568,True.intro,True.intro⟩⟩⟩,⟨sg40575,⟨sg40572,⟨sg40571,⟨sg40570,True.intro,True.intro⟩,True.intro⟩,⟨sg40574,⟨sg40573,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40578,⟨sg40577,⟨sg40576,True.intro,True.intro⟩,True.intro⟩,⟨sg40579,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_777All : degreeTree62_777.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40591,⟨sg40586,⟨sg40583,⟨sg40582,⟨sg40581,True.intro,True.intro⟩,True.intro⟩,⟨sg40585,⟨sg40584,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40589,⟨sg40588,⟨sg40587,True.intro,True.intro⟩,True.intro⟩,⟨sg40590,True.intro,True.intro⟩⟩⟩,⟨sg40597,⟨sg40594,⟨sg40593,⟨sg40592,True.intro,True.intro⟩,True.intro⟩,⟨sg40596,⟨sg40595,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40600,⟨sg40599,⟨sg40598,True.intro,True.intro⟩,True.intro⟩,⟨sg40601,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_778All : degreeTree62_778.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40580,degreeTree62_776All,degreeTree62_777All⟩

lemma degreeTree62_779All : degreeTree62_779.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40558,degreeTree62_775All,degreeTree62_778All⟩

lemma degreeTree62_780All : degreeTree62_780.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40514,degreeTree62_772All,degreeTree62_779All⟩

lemma degreeTree62_781All : degreeTree62_781.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40613,⟨sg40608,⟨sg40605,⟨sg40604,⟨sg40603,True.intro,True.intro⟩,True.intro⟩,⟨sg40607,⟨sg40606,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40611,⟨sg40610,⟨sg40609,True.intro,True.intro⟩,True.intro⟩,⟨sg40612,True.intro,True.intro⟩⟩⟩,⟨sg40619,⟨sg40616,⟨sg40615,⟨sg40614,True.intro,True.intro⟩,True.intro⟩,⟨sg40618,⟨sg40617,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40622,⟨sg40621,⟨sg40620,True.intro,True.intro⟩,True.intro⟩,⟨sg40623,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_782All : degreeTree62_782.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40635,⟨sg40630,⟨sg40627,⟨sg40626,⟨sg40625,True.intro,True.intro⟩,True.intro⟩,⟨sg40629,⟨sg40628,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40633,⟨sg40632,⟨sg40631,True.intro,True.intro⟩,True.intro⟩,⟨sg40634,True.intro,True.intro⟩⟩⟩,⟨sg40641,⟨sg40638,⟨sg40637,⟨sg40636,True.intro,True.intro⟩,True.intro⟩,⟨sg40640,⟨sg40639,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40644,⟨sg40643,⟨sg40642,True.intro,True.intro⟩,True.intro⟩,⟨sg40645,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_783All : degreeTree62_783.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40624,degreeTree62_781All,degreeTree62_782All⟩

lemma degreeTree62_784All : degreeTree62_784.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40657,⟨sg40652,⟨sg40649,⟨sg40648,⟨sg40647,True.intro,True.intro⟩,True.intro⟩,⟨sg40651,⟨sg40650,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40655,⟨sg40654,⟨sg40653,True.intro,True.intro⟩,True.intro⟩,⟨sg40656,True.intro,True.intro⟩⟩⟩,⟨sg40663,⟨sg40660,⟨sg40659,⟨sg40658,True.intro,True.intro⟩,True.intro⟩,⟨sg40662,⟨sg40661,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40666,⟨sg40665,⟨sg40664,True.intro,True.intro⟩,True.intro⟩,⟨sg40667,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_785All : degreeTree62_785.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40679,⟨sg40674,⟨sg40671,⟨sg40670,⟨sg40669,True.intro,True.intro⟩,True.intro⟩,⟨sg40673,⟨sg40672,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40677,⟨sg40676,⟨sg40675,True.intro,True.intro⟩,True.intro⟩,⟨sg40678,True.intro,True.intro⟩⟩⟩,⟨sg40685,⟨sg40682,⟨sg40681,⟨sg40680,True.intro,True.intro⟩,True.intro⟩,⟨sg40684,⟨sg40683,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40688,⟨sg40687,⟨sg40686,True.intro,True.intro⟩,True.intro⟩,⟨sg40689,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_786All : degreeTree62_786.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40668,degreeTree62_784All,degreeTree62_785All⟩

lemma degreeTree62_787All : degreeTree62_787.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40646,degreeTree62_783All,degreeTree62_786All⟩

lemma degreeTree62_788All : degreeTree62_788.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40701,⟨sg40696,⟨sg40693,⟨sg40692,⟨sg40691,True.intro,True.intro⟩,True.intro⟩,⟨sg40695,⟨sg40694,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40699,⟨sg40698,⟨sg40697,True.intro,True.intro⟩,True.intro⟩,⟨sg40700,True.intro,True.intro⟩⟩⟩,⟨sg40707,⟨sg40704,⟨sg40703,⟨sg40702,True.intro,True.intro⟩,True.intro⟩,⟨sg40706,⟨sg40705,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40710,⟨sg40709,⟨sg40708,True.intro,True.intro⟩,True.intro⟩,⟨sg40711,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_789All : degreeTree62_789.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40723,⟨sg40718,⟨sg40715,⟨sg40714,⟨sg40713,True.intro,True.intro⟩,True.intro⟩,⟨sg40717,⟨sg40716,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40721,⟨sg40720,⟨sg40719,True.intro,True.intro⟩,True.intro⟩,⟨sg40722,True.intro,True.intro⟩⟩⟩,⟨sg40729,⟨sg40726,⟨sg40725,⟨sg40724,True.intro,True.intro⟩,True.intro⟩,⟨sg40728,⟨sg40727,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40732,⟨sg40731,⟨sg40730,True.intro,True.intro⟩,True.intro⟩,⟨sg40733,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_790All : degreeTree62_790.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40712,degreeTree62_788All,degreeTree62_789All⟩

lemma degreeTree62_791All : degreeTree62_791.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40745,⟨sg40740,⟨sg40737,⟨sg40736,⟨sg40735,True.intro,True.intro⟩,True.intro⟩,⟨sg40739,⟨sg40738,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40743,⟨sg40742,⟨sg40741,True.intro,True.intro⟩,True.intro⟩,⟨sg40744,True.intro,True.intro⟩⟩⟩,⟨sg40751,⟨sg40748,⟨sg40747,⟨sg40746,True.intro,True.intro⟩,True.intro⟩,⟨sg40750,⟨sg40749,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40754,⟨sg40753,⟨sg40752,True.intro,True.intro⟩,True.intro⟩,⟨sg40755,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_792All : degreeTree62_792.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40767,⟨sg40762,⟨sg40759,⟨sg40758,⟨sg40757,True.intro,True.intro⟩,True.intro⟩,⟨sg40761,⟨sg40760,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40765,⟨sg40764,⟨sg40763,True.intro,True.intro⟩,True.intro⟩,⟨sg40766,True.intro,True.intro⟩⟩⟩,⟨sg40772,⟨sg40770,⟨sg40769,⟨sg40768,True.intro,True.intro⟩,True.intro⟩,⟨sg40771,True.intro,True.intro⟩⟩,⟨sg40775,⟨sg40774,⟨sg40773,True.intro,True.intro⟩,True.intro⟩,⟨sg40776,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_793All : degreeTree62_793.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40756,degreeTree62_791All,degreeTree62_792All⟩

lemma degreeTree62_794All : degreeTree62_794.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40734,degreeTree62_790All,degreeTree62_793All⟩

lemma degreeTree62_795All : degreeTree62_795.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40690,degreeTree62_787All,degreeTree62_794All⟩

lemma degreeTree62_796All : degreeTree62_796.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40602,degreeTree62_780All,degreeTree62_795All⟩

lemma degreeTree62_797All : degreeTree62_797.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40788,⟨sg40783,⟨sg40780,⟨sg40779,⟨sg40778,True.intro,True.intro⟩,True.intro⟩,⟨sg40782,⟨sg40781,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40786,⟨sg40785,⟨sg40784,True.intro,True.intro⟩,True.intro⟩,⟨sg40787,True.intro,True.intro⟩⟩⟩,⟨sg40794,⟨sg40791,⟨sg40790,⟨sg40789,True.intro,True.intro⟩,True.intro⟩,⟨sg40793,⟨sg40792,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40797,⟨sg40796,⟨sg40795,True.intro,True.intro⟩,True.intro⟩,⟨sg40798,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_798All : degreeTree62_798.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40810,⟨sg40805,⟨sg40802,⟨sg40801,⟨sg40800,True.intro,True.intro⟩,True.intro⟩,⟨sg40804,⟨sg40803,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40808,⟨sg40807,⟨sg40806,True.intro,True.intro⟩,True.intro⟩,⟨sg40809,True.intro,True.intro⟩⟩⟩,⟨sg40816,⟨sg40813,⟨sg40812,⟨sg40811,True.intro,True.intro⟩,True.intro⟩,⟨sg40815,⟨sg40814,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40819,⟨sg40818,⟨sg40817,True.intro,True.intro⟩,True.intro⟩,⟨sg40820,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_799All : degreeTree62_799.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40799,degreeTree62_797All,degreeTree62_798All⟩

lemma degreeTree62_800All : degreeTree62_800.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40832,⟨sg40827,⟨sg40824,⟨sg40823,⟨sg40822,True.intro,True.intro⟩,True.intro⟩,⟨sg40826,⟨sg40825,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40830,⟨sg40829,⟨sg40828,True.intro,True.intro⟩,True.intro⟩,⟨sg40831,True.intro,True.intro⟩⟩⟩,⟨sg40838,⟨sg40835,⟨sg40834,⟨sg40833,True.intro,True.intro⟩,True.intro⟩,⟨sg40837,⟨sg40836,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40841,⟨sg40840,⟨sg40839,True.intro,True.intro⟩,True.intro⟩,⟨sg40842,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_801All : degreeTree62_801.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40854,⟨sg40849,⟨sg40846,⟨sg40845,⟨sg40844,True.intro,True.intro⟩,True.intro⟩,⟨sg40848,⟨sg40847,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40852,⟨sg40851,⟨sg40850,True.intro,True.intro⟩,True.intro⟩,⟨sg40853,True.intro,True.intro⟩⟩⟩,⟨sg40860,⟨sg40857,⟨sg40856,⟨sg40855,True.intro,True.intro⟩,True.intro⟩,⟨sg40859,⟨sg40858,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40863,⟨sg40862,⟨sg40861,True.intro,True.intro⟩,True.intro⟩,⟨sg40864,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_802All : degreeTree62_802.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40843,degreeTree62_800All,degreeTree62_801All⟩

lemma degreeTree62_803All : degreeTree62_803.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40821,degreeTree62_799All,degreeTree62_802All⟩

lemma degreeTree62_804All : degreeTree62_804.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40876,⟨sg40871,⟨sg40868,⟨sg40867,⟨sg40866,True.intro,True.intro⟩,True.intro⟩,⟨sg40870,⟨sg40869,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40874,⟨sg40873,⟨sg40872,True.intro,True.intro⟩,True.intro⟩,⟨sg40875,True.intro,True.intro⟩⟩⟩,⟨sg40882,⟨sg40879,⟨sg40878,⟨sg40877,True.intro,True.intro⟩,True.intro⟩,⟨sg40881,⟨sg40880,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40885,⟨sg40884,⟨sg40883,True.intro,True.intro⟩,True.intro⟩,⟨sg40886,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_805All : degreeTree62_805.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40898,⟨sg40893,⟨sg40890,⟨sg40889,⟨sg40888,True.intro,True.intro⟩,True.intro⟩,⟨sg40892,⟨sg40891,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40896,⟨sg40895,⟨sg40894,True.intro,True.intro⟩,True.intro⟩,⟨sg40897,True.intro,True.intro⟩⟩⟩,⟨sg40904,⟨sg40901,⟨sg40900,⟨sg40899,True.intro,True.intro⟩,True.intro⟩,⟨sg40903,⟨sg40902,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40907,⟨sg40906,⟨sg40905,True.intro,True.intro⟩,True.intro⟩,⟨sg40908,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_806All : degreeTree62_806.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40887,degreeTree62_804All,degreeTree62_805All⟩

lemma degreeTree62_807All : degreeTree62_807.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40920,⟨sg40915,⟨sg40912,⟨sg40911,⟨sg40910,True.intro,True.intro⟩,True.intro⟩,⟨sg40914,⟨sg40913,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40918,⟨sg40917,⟨sg40916,True.intro,True.intro⟩,True.intro⟩,⟨sg40919,True.intro,True.intro⟩⟩⟩,⟨sg40926,⟨sg40923,⟨sg40922,⟨sg40921,True.intro,True.intro⟩,True.intro⟩,⟨sg40925,⟨sg40924,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40929,⟨sg40928,⟨sg40927,True.intro,True.intro⟩,True.intro⟩,⟨sg40930,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_808All : degreeTree62_808.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40942,⟨sg40937,⟨sg40934,⟨sg40933,⟨sg40932,True.intro,True.intro⟩,True.intro⟩,⟨sg40936,⟨sg40935,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40940,⟨sg40939,⟨sg40938,True.intro,True.intro⟩,True.intro⟩,⟨sg40941,True.intro,True.intro⟩⟩⟩,⟨sg40948,⟨sg40945,⟨sg40944,⟨sg40943,True.intro,True.intro⟩,True.intro⟩,⟨sg40947,⟨sg40946,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40951,⟨sg40950,⟨sg40949,True.intro,True.intro⟩,True.intro⟩,⟨sg40952,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_809All : degreeTree62_809.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40931,degreeTree62_807All,degreeTree62_808All⟩

lemma degreeTree62_810All : degreeTree62_810.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40909,degreeTree62_806All,degreeTree62_809All⟩

lemma degreeTree62_811All : degreeTree62_811.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40865,degreeTree62_803All,degreeTree62_810All⟩

lemma degreeTree62_812All : degreeTree62_812.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40964,⟨sg40959,⟨sg40956,⟨sg40955,⟨sg40954,True.intro,True.intro⟩,True.intro⟩,⟨sg40958,⟨sg40957,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40962,⟨sg40961,⟨sg40960,True.intro,True.intro⟩,True.intro⟩,⟨sg40963,True.intro,True.intro⟩⟩⟩,⟨sg40970,⟨sg40967,⟨sg40966,⟨sg40965,True.intro,True.intro⟩,True.intro⟩,⟨sg40969,⟨sg40968,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40973,⟨sg40972,⟨sg40971,True.intro,True.intro⟩,True.intro⟩,⟨sg40974,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_813All : degreeTree62_813.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40986,⟨sg40981,⟨sg40978,⟨sg40977,⟨sg40976,True.intro,True.intro⟩,True.intro⟩,⟨sg40980,⟨sg40979,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40984,⟨sg40983,⟨sg40982,True.intro,True.intro⟩,True.intro⟩,⟨sg40985,True.intro,True.intro⟩⟩⟩,⟨sg40992,⟨sg40989,⟨sg40988,⟨sg40987,True.intro,True.intro⟩,True.intro⟩,⟨sg40991,⟨sg40990,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg40995,⟨sg40994,⟨sg40993,True.intro,True.intro⟩,True.intro⟩,⟨sg40996,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_814All : degreeTree62_814.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40975,degreeTree62_812All,degreeTree62_813All⟩

lemma degreeTree62_815All : degreeTree62_815.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41008,⟨sg41003,⟨sg41000,⟨sg40999,⟨sg40998,True.intro,True.intro⟩,True.intro⟩,⟨sg41002,⟨sg41001,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41006,⟨sg41005,⟨sg41004,True.intro,True.intro⟩,True.intro⟩,⟨sg41007,True.intro,True.intro⟩⟩⟩,⟨sg41014,⟨sg41011,⟨sg41010,⟨sg41009,True.intro,True.intro⟩,True.intro⟩,⟨sg41013,⟨sg41012,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41017,⟨sg41016,⟨sg41015,True.intro,True.intro⟩,True.intro⟩,⟨sg41018,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_816All : degreeTree62_816.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41030,⟨sg41025,⟨sg41022,⟨sg41021,⟨sg41020,True.intro,True.intro⟩,True.intro⟩,⟨sg41024,⟨sg41023,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41028,⟨sg41027,⟨sg41026,True.intro,True.intro⟩,True.intro⟩,⟨sg41029,True.intro,True.intro⟩⟩⟩,⟨sg41036,⟨sg41033,⟨sg41032,⟨sg41031,True.intro,True.intro⟩,True.intro⟩,⟨sg41035,⟨sg41034,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41039,⟨sg41038,⟨sg41037,True.intro,True.intro⟩,True.intro⟩,⟨sg41040,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_817All : degreeTree62_817.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41019,degreeTree62_815All,degreeTree62_816All⟩

lemma degreeTree62_818All : degreeTree62_818.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40997,degreeTree62_814All,degreeTree62_817All⟩

lemma degreeTree62_819All : degreeTree62_819.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41052,⟨sg41047,⟨sg41044,⟨sg41043,⟨sg41042,True.intro,True.intro⟩,True.intro⟩,⟨sg41046,⟨sg41045,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41050,⟨sg41049,⟨sg41048,True.intro,True.intro⟩,True.intro⟩,⟨sg41051,True.intro,True.intro⟩⟩⟩,⟨sg41058,⟨sg41055,⟨sg41054,⟨sg41053,True.intro,True.intro⟩,True.intro⟩,⟨sg41057,⟨sg41056,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41061,⟨sg41060,⟨sg41059,True.intro,True.intro⟩,True.intro⟩,⟨sg41062,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_820All : degreeTree62_820.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41074,⟨sg41069,⟨sg41066,⟨sg41065,⟨sg41064,True.intro,True.intro⟩,True.intro⟩,⟨sg41068,⟨sg41067,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41072,⟨sg41071,⟨sg41070,True.intro,True.intro⟩,True.intro⟩,⟨sg41073,True.intro,True.intro⟩⟩⟩,⟨sg41080,⟨sg41077,⟨sg41076,⟨sg41075,True.intro,True.intro⟩,True.intro⟩,⟨sg41079,⟨sg41078,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41083,⟨sg41082,⟨sg41081,True.intro,True.intro⟩,True.intro⟩,⟨sg41084,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_821All : degreeTree62_821.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41063,degreeTree62_819All,degreeTree62_820All⟩

lemma degreeTree62_822All : degreeTree62_822.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41096,⟨sg41091,⟨sg41088,⟨sg41087,⟨sg41086,True.intro,True.intro⟩,True.intro⟩,⟨sg41090,⟨sg41089,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41094,⟨sg41093,⟨sg41092,True.intro,True.intro⟩,True.intro⟩,⟨sg41095,True.intro,True.intro⟩⟩⟩,⟨sg41102,⟨sg41099,⟨sg41098,⟨sg41097,True.intro,True.intro⟩,True.intro⟩,⟨sg41101,⟨sg41100,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41105,⟨sg41104,⟨sg41103,True.intro,True.intro⟩,True.intro⟩,⟨sg41106,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_823All : degreeTree62_823.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41118,⟨sg41113,⟨sg41110,⟨sg41109,⟨sg41108,True.intro,True.intro⟩,True.intro⟩,⟨sg41112,⟨sg41111,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41116,⟨sg41115,⟨sg41114,True.intro,True.intro⟩,True.intro⟩,⟨sg41117,True.intro,True.intro⟩⟩⟩,⟨sg41123,⟨sg41121,⟨sg41120,⟨sg41119,True.intro,True.intro⟩,True.intro⟩,⟨sg41122,True.intro,True.intro⟩⟩,⟨sg41126,⟨sg41125,⟨sg41124,True.intro,True.intro⟩,True.intro⟩,⟨sg41127,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_824All : degreeTree62_824.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41107,degreeTree62_822All,degreeTree62_823All⟩

lemma degreeTree62_825All : degreeTree62_825.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41085,degreeTree62_821All,degreeTree62_824All⟩

lemma degreeTree62_826All : degreeTree62_826.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41041,degreeTree62_818All,degreeTree62_825All⟩

lemma degreeTree62_827All : degreeTree62_827.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40953,degreeTree62_811All,degreeTree62_826All⟩

lemma degreeTree62_828All : degreeTree62_828.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40777,degreeTree62_796All,degreeTree62_827All⟩

lemma degreeTree62_829All : degreeTree62_829.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41139,⟨sg41134,⟨sg41131,⟨sg41130,⟨sg41129,True.intro,True.intro⟩,True.intro⟩,⟨sg41133,⟨sg41132,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41137,⟨sg41136,⟨sg41135,True.intro,True.intro⟩,True.intro⟩,⟨sg41138,True.intro,True.intro⟩⟩⟩,⟨sg41145,⟨sg41142,⟨sg41141,⟨sg41140,True.intro,True.intro⟩,True.intro⟩,⟨sg41144,⟨sg41143,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41148,⟨sg41147,⟨sg41146,True.intro,True.intro⟩,True.intro⟩,⟨sg41149,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_830All : degreeTree62_830.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41161,⟨sg41156,⟨sg41153,⟨sg41152,⟨sg41151,True.intro,True.intro⟩,True.intro⟩,⟨sg41155,⟨sg41154,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41159,⟨sg41158,⟨sg41157,True.intro,True.intro⟩,True.intro⟩,⟨sg41160,True.intro,True.intro⟩⟩⟩,⟨sg41167,⟨sg41164,⟨sg41163,⟨sg41162,True.intro,True.intro⟩,True.intro⟩,⟨sg41166,⟨sg41165,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41170,⟨sg41169,⟨sg41168,True.intro,True.intro⟩,True.intro⟩,⟨sg41171,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_831All : degreeTree62_831.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41150,degreeTree62_829All,degreeTree62_830All⟩

lemma degreeTree62_832All : degreeTree62_832.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41183,⟨sg41178,⟨sg41175,⟨sg41174,⟨sg41173,True.intro,True.intro⟩,True.intro⟩,⟨sg41177,⟨sg41176,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41181,⟨sg41180,⟨sg41179,True.intro,True.intro⟩,True.intro⟩,⟨sg41182,True.intro,True.intro⟩⟩⟩,⟨sg41189,⟨sg41186,⟨sg41185,⟨sg41184,True.intro,True.intro⟩,True.intro⟩,⟨sg41188,⟨sg41187,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41192,⟨sg41191,⟨sg41190,True.intro,True.intro⟩,True.intro⟩,⟨sg41193,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_833All : degreeTree62_833.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41205,⟨sg41200,⟨sg41197,⟨sg41196,⟨sg41195,True.intro,True.intro⟩,True.intro⟩,⟨sg41199,⟨sg41198,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41203,⟨sg41202,⟨sg41201,True.intro,True.intro⟩,True.intro⟩,⟨sg41204,True.intro,True.intro⟩⟩⟩,⟨sg41211,⟨sg41208,⟨sg41207,⟨sg41206,True.intro,True.intro⟩,True.intro⟩,⟨sg41210,⟨sg41209,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41214,⟨sg41213,⟨sg41212,True.intro,True.intro⟩,True.intro⟩,⟨sg41215,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_834All : degreeTree62_834.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41194,degreeTree62_832All,degreeTree62_833All⟩

lemma degreeTree62_835All : degreeTree62_835.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41172,degreeTree62_831All,degreeTree62_834All⟩

lemma degreeTree62_836All : degreeTree62_836.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41227,⟨sg41222,⟨sg41219,⟨sg41218,⟨sg41217,True.intro,True.intro⟩,True.intro⟩,⟨sg41221,⟨sg41220,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41225,⟨sg41224,⟨sg41223,True.intro,True.intro⟩,True.intro⟩,⟨sg41226,True.intro,True.intro⟩⟩⟩,⟨sg41233,⟨sg41230,⟨sg41229,⟨sg41228,True.intro,True.intro⟩,True.intro⟩,⟨sg41232,⟨sg41231,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41236,⟨sg41235,⟨sg41234,True.intro,True.intro⟩,True.intro⟩,⟨sg41237,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_837All : degreeTree62_837.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41249,⟨sg41244,⟨sg41241,⟨sg41240,⟨sg41239,True.intro,True.intro⟩,True.intro⟩,⟨sg41243,⟨sg41242,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41247,⟨sg41246,⟨sg41245,True.intro,True.intro⟩,True.intro⟩,⟨sg41248,True.intro,True.intro⟩⟩⟩,⟨sg41255,⟨sg41252,⟨sg41251,⟨sg41250,True.intro,True.intro⟩,True.intro⟩,⟨sg41254,⟨sg41253,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41258,⟨sg41257,⟨sg41256,True.intro,True.intro⟩,True.intro⟩,⟨sg41259,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_838All : degreeTree62_838.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41238,degreeTree62_836All,degreeTree62_837All⟩

lemma degreeTree62_839All : degreeTree62_839.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41271,⟨sg41266,⟨sg41263,⟨sg41262,⟨sg41261,True.intro,True.intro⟩,True.intro⟩,⟨sg41265,⟨sg41264,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41269,⟨sg41268,⟨sg41267,True.intro,True.intro⟩,True.intro⟩,⟨sg41270,True.intro,True.intro⟩⟩⟩,⟨sg41277,⟨sg41274,⟨sg41273,⟨sg41272,True.intro,True.intro⟩,True.intro⟩,⟨sg41276,⟨sg41275,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41280,⟨sg41279,⟨sg41278,True.intro,True.intro⟩,True.intro⟩,⟨sg41281,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_840All : degreeTree62_840.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41293,⟨sg41288,⟨sg41285,⟨sg41284,⟨sg41283,True.intro,True.intro⟩,True.intro⟩,⟨sg41287,⟨sg41286,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41291,⟨sg41290,⟨sg41289,True.intro,True.intro⟩,True.intro⟩,⟨sg41292,True.intro,True.intro⟩⟩⟩,⟨sg41299,⟨sg41296,⟨sg41295,⟨sg41294,True.intro,True.intro⟩,True.intro⟩,⟨sg41298,⟨sg41297,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41302,⟨sg41301,⟨sg41300,True.intro,True.intro⟩,True.intro⟩,⟨sg41303,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_841All : degreeTree62_841.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41282,degreeTree62_839All,degreeTree62_840All⟩

lemma degreeTree62_842All : degreeTree62_842.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41260,degreeTree62_838All,degreeTree62_841All⟩

lemma degreeTree62_843All : degreeTree62_843.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41216,degreeTree62_835All,degreeTree62_842All⟩

lemma degreeTree62_844All : degreeTree62_844.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41315,⟨sg41310,⟨sg41307,⟨sg41306,⟨sg41305,True.intro,True.intro⟩,True.intro⟩,⟨sg41309,⟨sg41308,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41313,⟨sg41312,⟨sg41311,True.intro,True.intro⟩,True.intro⟩,⟨sg41314,True.intro,True.intro⟩⟩⟩,⟨sg41321,⟨sg41318,⟨sg41317,⟨sg41316,True.intro,True.intro⟩,True.intro⟩,⟨sg41320,⟨sg41319,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41324,⟨sg41323,⟨sg41322,True.intro,True.intro⟩,True.intro⟩,⟨sg41325,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_845All : degreeTree62_845.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41337,⟨sg41332,⟨sg41329,⟨sg41328,⟨sg41327,True.intro,True.intro⟩,True.intro⟩,⟨sg41331,⟨sg41330,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41335,⟨sg41334,⟨sg41333,True.intro,True.intro⟩,True.intro⟩,⟨sg41336,True.intro,True.intro⟩⟩⟩,⟨sg41343,⟨sg41340,⟨sg41339,⟨sg41338,True.intro,True.intro⟩,True.intro⟩,⟨sg41342,⟨sg41341,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41346,⟨sg41345,⟨sg41344,True.intro,True.intro⟩,True.intro⟩,⟨sg41347,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_846All : degreeTree62_846.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41326,degreeTree62_844All,degreeTree62_845All⟩

lemma degreeTree62_847All : degreeTree62_847.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41359,⟨sg41354,⟨sg41351,⟨sg41350,⟨sg41349,True.intro,True.intro⟩,True.intro⟩,⟨sg41353,⟨sg41352,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41357,⟨sg41356,⟨sg41355,True.intro,True.intro⟩,True.intro⟩,⟨sg41358,True.intro,True.intro⟩⟩⟩,⟨sg41365,⟨sg41362,⟨sg41361,⟨sg41360,True.intro,True.intro⟩,True.intro⟩,⟨sg41364,⟨sg41363,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41368,⟨sg41367,⟨sg41366,True.intro,True.intro⟩,True.intro⟩,⟨sg41369,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_848All : degreeTree62_848.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41381,⟨sg41376,⟨sg41373,⟨sg41372,⟨sg41371,True.intro,True.intro⟩,True.intro⟩,⟨sg41375,⟨sg41374,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41379,⟨sg41378,⟨sg41377,True.intro,True.intro⟩,True.intro⟩,⟨sg41380,True.intro,True.intro⟩⟩⟩,⟨sg41387,⟨sg41384,⟨sg41383,⟨sg41382,True.intro,True.intro⟩,True.intro⟩,⟨sg41386,⟨sg41385,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41390,⟨sg41389,⟨sg41388,True.intro,True.intro⟩,True.intro⟩,⟨sg41391,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_849All : degreeTree62_849.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41370,degreeTree62_847All,degreeTree62_848All⟩

lemma degreeTree62_850All : degreeTree62_850.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41348,degreeTree62_846All,degreeTree62_849All⟩

lemma degreeTree62_851All : degreeTree62_851.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41403,⟨sg41398,⟨sg41395,⟨sg41394,⟨sg41393,True.intro,True.intro⟩,True.intro⟩,⟨sg41397,⟨sg41396,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41401,⟨sg41400,⟨sg41399,True.intro,True.intro⟩,True.intro⟩,⟨sg41402,True.intro,True.intro⟩⟩⟩,⟨sg41409,⟨sg41406,⟨sg41405,⟨sg41404,True.intro,True.intro⟩,True.intro⟩,⟨sg41408,⟨sg41407,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41412,⟨sg41411,⟨sg41410,True.intro,True.intro⟩,True.intro⟩,⟨sg41413,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_852All : degreeTree62_852.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41425,⟨sg41420,⟨sg41417,⟨sg41416,⟨sg41415,True.intro,True.intro⟩,True.intro⟩,⟨sg41419,⟨sg41418,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41423,⟨sg41422,⟨sg41421,True.intro,True.intro⟩,True.intro⟩,⟨sg41424,True.intro,True.intro⟩⟩⟩,⟨sg41431,⟨sg41428,⟨sg41427,⟨sg41426,True.intro,True.intro⟩,True.intro⟩,⟨sg41430,⟨sg41429,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41434,⟨sg41433,⟨sg41432,True.intro,True.intro⟩,True.intro⟩,⟨sg41435,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_853All : degreeTree62_853.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41414,degreeTree62_851All,degreeTree62_852All⟩

lemma degreeTree62_854All : degreeTree62_854.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41447,⟨sg41442,⟨sg41439,⟨sg41438,⟨sg41437,True.intro,True.intro⟩,True.intro⟩,⟨sg41441,⟨sg41440,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41445,⟨sg41444,⟨sg41443,True.intro,True.intro⟩,True.intro⟩,⟨sg41446,True.intro,True.intro⟩⟩⟩,⟨sg41453,⟨sg41450,⟨sg41449,⟨sg41448,True.intro,True.intro⟩,True.intro⟩,⟨sg41452,⟨sg41451,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41456,⟨sg41455,⟨sg41454,True.intro,True.intro⟩,True.intro⟩,⟨sg41457,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_855All : degreeTree62_855.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41469,⟨sg41464,⟨sg41461,⟨sg41460,⟨sg41459,True.intro,True.intro⟩,True.intro⟩,⟨sg41463,⟨sg41462,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41467,⟨sg41466,⟨sg41465,True.intro,True.intro⟩,True.intro⟩,⟨sg41468,True.intro,True.intro⟩⟩⟩,⟨sg41474,⟨sg41472,⟨sg41471,⟨sg41470,True.intro,True.intro⟩,True.intro⟩,⟨sg41473,True.intro,True.intro⟩⟩,⟨sg41477,⟨sg41476,⟨sg41475,True.intro,True.intro⟩,True.intro⟩,⟨sg41478,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_856All : degreeTree62_856.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41458,degreeTree62_854All,degreeTree62_855All⟩

lemma degreeTree62_857All : degreeTree62_857.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41436,degreeTree62_853All,degreeTree62_856All⟩

lemma degreeTree62_858All : degreeTree62_858.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41392,degreeTree62_850All,degreeTree62_857All⟩

lemma degreeTree62_859All : degreeTree62_859.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41304,degreeTree62_843All,degreeTree62_858All⟩

lemma degreeTree62_860All : degreeTree62_860.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41490,⟨sg41485,⟨sg41482,⟨sg41481,⟨sg41480,True.intro,True.intro⟩,True.intro⟩,⟨sg41484,⟨sg41483,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41488,⟨sg41487,⟨sg41486,True.intro,True.intro⟩,True.intro⟩,⟨sg41489,True.intro,True.intro⟩⟩⟩,⟨sg41496,⟨sg41493,⟨sg41492,⟨sg41491,True.intro,True.intro⟩,True.intro⟩,⟨sg41495,⟨sg41494,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41499,⟨sg41498,⟨sg41497,True.intro,True.intro⟩,True.intro⟩,⟨sg41500,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_861All : degreeTree62_861.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41512,⟨sg41507,⟨sg41504,⟨sg41503,⟨sg41502,True.intro,True.intro⟩,True.intro⟩,⟨sg41506,⟨sg41505,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41510,⟨sg41509,⟨sg41508,True.intro,True.intro⟩,True.intro⟩,⟨sg41511,True.intro,True.intro⟩⟩⟩,⟨sg41518,⟨sg41515,⟨sg41514,⟨sg41513,True.intro,True.intro⟩,True.intro⟩,⟨sg41517,⟨sg41516,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41521,⟨sg41520,⟨sg41519,True.intro,True.intro⟩,True.intro⟩,⟨sg41522,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_862All : degreeTree62_862.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41501,degreeTree62_860All,degreeTree62_861All⟩

lemma degreeTree62_863All : degreeTree62_863.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41534,⟨sg41529,⟨sg41526,⟨sg41525,⟨sg41524,True.intro,True.intro⟩,True.intro⟩,⟨sg41528,⟨sg41527,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41532,⟨sg41531,⟨sg41530,True.intro,True.intro⟩,True.intro⟩,⟨sg41533,True.intro,True.intro⟩⟩⟩,⟨sg41540,⟨sg41537,⟨sg41536,⟨sg41535,True.intro,True.intro⟩,True.intro⟩,⟨sg41539,⟨sg41538,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41543,⟨sg41542,⟨sg41541,True.intro,True.intro⟩,True.intro⟩,⟨sg41544,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_864All : degreeTree62_864.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41556,⟨sg41551,⟨sg41548,⟨sg41547,⟨sg41546,True.intro,True.intro⟩,True.intro⟩,⟨sg41550,⟨sg41549,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41554,⟨sg41553,⟨sg41552,True.intro,True.intro⟩,True.intro⟩,⟨sg41555,True.intro,True.intro⟩⟩⟩,⟨sg41562,⟨sg41559,⟨sg41558,⟨sg41557,True.intro,True.intro⟩,True.intro⟩,⟨sg41561,⟨sg41560,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41565,⟨sg41564,⟨sg41563,True.intro,True.intro⟩,True.intro⟩,⟨sg41566,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_865All : degreeTree62_865.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41545,degreeTree62_863All,degreeTree62_864All⟩

lemma degreeTree62_866All : degreeTree62_866.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41523,degreeTree62_862All,degreeTree62_865All⟩

lemma degreeTree62_867All : degreeTree62_867.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41578,⟨sg41573,⟨sg41570,⟨sg41569,⟨sg41568,True.intro,True.intro⟩,True.intro⟩,⟨sg41572,⟨sg41571,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41576,⟨sg41575,⟨sg41574,True.intro,True.intro⟩,True.intro⟩,⟨sg41577,True.intro,True.intro⟩⟩⟩,⟨sg41584,⟨sg41581,⟨sg41580,⟨sg41579,True.intro,True.intro⟩,True.intro⟩,⟨sg41583,⟨sg41582,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41587,⟨sg41586,⟨sg41585,True.intro,True.intro⟩,True.intro⟩,⟨sg41588,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_868All : degreeTree62_868.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41600,⟨sg41595,⟨sg41592,⟨sg41591,⟨sg41590,True.intro,True.intro⟩,True.intro⟩,⟨sg41594,⟨sg41593,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41598,⟨sg41597,⟨sg41596,True.intro,True.intro⟩,True.intro⟩,⟨sg41599,True.intro,True.intro⟩⟩⟩,⟨sg41606,⟨sg41603,⟨sg41602,⟨sg41601,True.intro,True.intro⟩,True.intro⟩,⟨sg41605,⟨sg41604,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41609,⟨sg41608,⟨sg41607,True.intro,True.intro⟩,True.intro⟩,⟨sg41610,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_869All : degreeTree62_869.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41589,degreeTree62_867All,degreeTree62_868All⟩

lemma degreeTree62_870All : degreeTree62_870.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41622,⟨sg41617,⟨sg41614,⟨sg41613,⟨sg41612,True.intro,True.intro⟩,True.intro⟩,⟨sg41616,⟨sg41615,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41620,⟨sg41619,⟨sg41618,True.intro,True.intro⟩,True.intro⟩,⟨sg41621,True.intro,True.intro⟩⟩⟩,⟨sg41628,⟨sg41625,⟨sg41624,⟨sg41623,True.intro,True.intro⟩,True.intro⟩,⟨sg41627,⟨sg41626,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41631,⟨sg41630,⟨sg41629,True.intro,True.intro⟩,True.intro⟩,⟨sg41632,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_871All : degreeTree62_871.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41644,⟨sg41639,⟨sg41636,⟨sg41635,⟨sg41634,True.intro,True.intro⟩,True.intro⟩,⟨sg41638,⟨sg41637,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41642,⟨sg41641,⟨sg41640,True.intro,True.intro⟩,True.intro⟩,⟨sg41643,True.intro,True.intro⟩⟩⟩,⟨sg41650,⟨sg41647,⟨sg41646,⟨sg41645,True.intro,True.intro⟩,True.intro⟩,⟨sg41649,⟨sg41648,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41653,⟨sg41652,⟨sg41651,True.intro,True.intro⟩,True.intro⟩,⟨sg41654,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_872All : degreeTree62_872.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41633,degreeTree62_870All,degreeTree62_871All⟩

lemma degreeTree62_873All : degreeTree62_873.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41611,degreeTree62_869All,degreeTree62_872All⟩

lemma degreeTree62_874All : degreeTree62_874.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41567,degreeTree62_866All,degreeTree62_873All⟩

lemma degreeTree62_875All : degreeTree62_875.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41666,⟨sg41661,⟨sg41658,⟨sg41657,⟨sg41656,True.intro,True.intro⟩,True.intro⟩,⟨sg41660,⟨sg41659,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41664,⟨sg41663,⟨sg41662,True.intro,True.intro⟩,True.intro⟩,⟨sg41665,True.intro,True.intro⟩⟩⟩,⟨sg41672,⟨sg41669,⟨sg41668,⟨sg41667,True.intro,True.intro⟩,True.intro⟩,⟨sg41671,⟨sg41670,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41675,⟨sg41674,⟨sg41673,True.intro,True.intro⟩,True.intro⟩,⟨sg41676,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_876All : degreeTree62_876.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41688,⟨sg41683,⟨sg41680,⟨sg41679,⟨sg41678,True.intro,True.intro⟩,True.intro⟩,⟨sg41682,⟨sg41681,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41686,⟨sg41685,⟨sg41684,True.intro,True.intro⟩,True.intro⟩,⟨sg41687,True.intro,True.intro⟩⟩⟩,⟨sg41694,⟨sg41691,⟨sg41690,⟨sg41689,True.intro,True.intro⟩,True.intro⟩,⟨sg41693,⟨sg41692,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41697,⟨sg41696,⟨sg41695,True.intro,True.intro⟩,True.intro⟩,⟨sg41698,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_877All : degreeTree62_877.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41677,degreeTree62_875All,degreeTree62_876All⟩

lemma degreeTree62_878All : degreeTree62_878.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41710,⟨sg41705,⟨sg41702,⟨sg41701,⟨sg41700,True.intro,True.intro⟩,True.intro⟩,⟨sg41704,⟨sg41703,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41708,⟨sg41707,⟨sg41706,True.intro,True.intro⟩,True.intro⟩,⟨sg41709,True.intro,True.intro⟩⟩⟩,⟨sg41716,⟨sg41713,⟨sg41712,⟨sg41711,True.intro,True.intro⟩,True.intro⟩,⟨sg41715,⟨sg41714,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41719,⟨sg41718,⟨sg41717,True.intro,True.intro⟩,True.intro⟩,⟨sg41720,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_879All : degreeTree62_879.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41732,⟨sg41727,⟨sg41724,⟨sg41723,⟨sg41722,True.intro,True.intro⟩,True.intro⟩,⟨sg41726,⟨sg41725,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41730,⟨sg41729,⟨sg41728,True.intro,True.intro⟩,True.intro⟩,⟨sg41731,True.intro,True.intro⟩⟩⟩,⟨sg41738,⟨sg41735,⟨sg41734,⟨sg41733,True.intro,True.intro⟩,True.intro⟩,⟨sg41737,⟨sg41736,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41741,⟨sg41740,⟨sg41739,True.intro,True.intro⟩,True.intro⟩,⟨sg41742,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_880All : degreeTree62_880.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41721,degreeTree62_878All,degreeTree62_879All⟩

lemma degreeTree62_881All : degreeTree62_881.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41699,degreeTree62_877All,degreeTree62_880All⟩

lemma degreeTree62_882All : degreeTree62_882.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41754,⟨sg41749,⟨sg41746,⟨sg41745,⟨sg41744,True.intro,True.intro⟩,True.intro⟩,⟨sg41748,⟨sg41747,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41752,⟨sg41751,⟨sg41750,True.intro,True.intro⟩,True.intro⟩,⟨sg41753,True.intro,True.intro⟩⟩⟩,⟨sg41760,⟨sg41757,⟨sg41756,⟨sg41755,True.intro,True.intro⟩,True.intro⟩,⟨sg41759,⟨sg41758,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41763,⟨sg41762,⟨sg41761,True.intro,True.intro⟩,True.intro⟩,⟨sg41764,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_883All : degreeTree62_883.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41776,⟨sg41771,⟨sg41768,⟨sg41767,⟨sg41766,True.intro,True.intro⟩,True.intro⟩,⟨sg41770,⟨sg41769,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41774,⟨sg41773,⟨sg41772,True.intro,True.intro⟩,True.intro⟩,⟨sg41775,True.intro,True.intro⟩⟩⟩,⟨sg41782,⟨sg41779,⟨sg41778,⟨sg41777,True.intro,True.intro⟩,True.intro⟩,⟨sg41781,⟨sg41780,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41785,⟨sg41784,⟨sg41783,True.intro,True.intro⟩,True.intro⟩,⟨sg41786,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_884All : degreeTree62_884.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41765,degreeTree62_882All,degreeTree62_883All⟩

lemma degreeTree62_885All : degreeTree62_885.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41798,⟨sg41793,⟨sg41790,⟨sg41789,⟨sg41788,True.intro,True.intro⟩,True.intro⟩,⟨sg41792,⟨sg41791,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41796,⟨sg41795,⟨sg41794,True.intro,True.intro⟩,True.intro⟩,⟨sg41797,True.intro,True.intro⟩⟩⟩,⟨sg41804,⟨sg41801,⟨sg41800,⟨sg41799,True.intro,True.intro⟩,True.intro⟩,⟨sg41803,⟨sg41802,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41807,⟨sg41806,⟨sg41805,True.intro,True.intro⟩,True.intro⟩,⟨sg41808,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_886All : degreeTree62_886.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41820,⟨sg41815,⟨sg41812,⟨sg41811,⟨sg41810,True.intro,True.intro⟩,True.intro⟩,⟨sg41814,⟨sg41813,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41818,⟨sg41817,⟨sg41816,True.intro,True.intro⟩,True.intro⟩,⟨sg41819,True.intro,True.intro⟩⟩⟩,⟨sg41825,⟨sg41823,⟨sg41822,⟨sg41821,True.intro,True.intro⟩,True.intro⟩,⟨sg41824,True.intro,True.intro⟩⟩,⟨sg41828,⟨sg41827,⟨sg41826,True.intro,True.intro⟩,True.intro⟩,⟨sg41829,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_887All : degreeTree62_887.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41809,degreeTree62_885All,degreeTree62_886All⟩

lemma degreeTree62_888All : degreeTree62_888.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41787,degreeTree62_884All,degreeTree62_887All⟩

lemma degreeTree62_889All : degreeTree62_889.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41743,degreeTree62_881All,degreeTree62_888All⟩

lemma degreeTree62_890All : degreeTree62_890.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41655,degreeTree62_874All,degreeTree62_889All⟩

lemma degreeTree62_891All : degreeTree62_891.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41479,degreeTree62_859All,degreeTree62_890All⟩

lemma degreeTree62_892All : degreeTree62_892.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41128,degreeTree62_828All,degreeTree62_891All⟩

lemma degreeTree62_893All : degreeTree62_893.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41841,⟨sg41836,⟨sg41833,⟨sg41832,⟨sg41831,True.intro,True.intro⟩,True.intro⟩,⟨sg41835,⟨sg41834,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41839,⟨sg41838,⟨sg41837,True.intro,True.intro⟩,True.intro⟩,⟨sg41840,True.intro,True.intro⟩⟩⟩,⟨sg41847,⟨sg41844,⟨sg41843,⟨sg41842,True.intro,True.intro⟩,True.intro⟩,⟨sg41846,⟨sg41845,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41850,⟨sg41849,⟨sg41848,True.intro,True.intro⟩,True.intro⟩,⟨sg41851,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_894All : degreeTree62_894.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41863,⟨sg41858,⟨sg41855,⟨sg41854,⟨sg41853,True.intro,True.intro⟩,True.intro⟩,⟨sg41857,⟨sg41856,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41861,⟨sg41860,⟨sg41859,True.intro,True.intro⟩,True.intro⟩,⟨sg41862,True.intro,True.intro⟩⟩⟩,⟨sg41869,⟨sg41866,⟨sg41865,⟨sg41864,True.intro,True.intro⟩,True.intro⟩,⟨sg41868,⟨sg41867,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41872,⟨sg41871,⟨sg41870,True.intro,True.intro⟩,True.intro⟩,⟨sg41873,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_895All : degreeTree62_895.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41852,degreeTree62_893All,degreeTree62_894All⟩

lemma degreeTree62_896All : degreeTree62_896.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41885,⟨sg41880,⟨sg41877,⟨sg41876,⟨sg41875,True.intro,True.intro⟩,True.intro⟩,⟨sg41879,⟨sg41878,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41883,⟨sg41882,⟨sg41881,True.intro,True.intro⟩,True.intro⟩,⟨sg41884,True.intro,True.intro⟩⟩⟩,⟨sg41891,⟨sg41888,⟨sg41887,⟨sg41886,True.intro,True.intro⟩,True.intro⟩,⟨sg41890,⟨sg41889,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41894,⟨sg41893,⟨sg41892,True.intro,True.intro⟩,True.intro⟩,⟨sg41895,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_897All : degreeTree62_897.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41907,⟨sg41902,⟨sg41899,⟨sg41898,⟨sg41897,True.intro,True.intro⟩,True.intro⟩,⟨sg41901,⟨sg41900,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41905,⟨sg41904,⟨sg41903,True.intro,True.intro⟩,True.intro⟩,⟨sg41906,True.intro,True.intro⟩⟩⟩,⟨sg41913,⟨sg41910,⟨sg41909,⟨sg41908,True.intro,True.intro⟩,True.intro⟩,⟨sg41912,⟨sg41911,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41916,⟨sg41915,⟨sg41914,True.intro,True.intro⟩,True.intro⟩,⟨sg41917,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_898All : degreeTree62_898.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41896,degreeTree62_896All,degreeTree62_897All⟩

lemma degreeTree62_899All : degreeTree62_899.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41874,degreeTree62_895All,degreeTree62_898All⟩

lemma degreeTree62_900All : degreeTree62_900.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41929,⟨sg41924,⟨sg41921,⟨sg41920,⟨sg41919,True.intro,True.intro⟩,True.intro⟩,⟨sg41923,⟨sg41922,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41927,⟨sg41926,⟨sg41925,True.intro,True.intro⟩,True.intro⟩,⟨sg41928,True.intro,True.intro⟩⟩⟩,⟨sg41935,⟨sg41932,⟨sg41931,⟨sg41930,True.intro,True.intro⟩,True.intro⟩,⟨sg41934,⟨sg41933,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41938,⟨sg41937,⟨sg41936,True.intro,True.intro⟩,True.intro⟩,⟨sg41939,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_901All : degreeTree62_901.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41951,⟨sg41946,⟨sg41943,⟨sg41942,⟨sg41941,True.intro,True.intro⟩,True.intro⟩,⟨sg41945,⟨sg41944,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41949,⟨sg41948,⟨sg41947,True.intro,True.intro⟩,True.intro⟩,⟨sg41950,True.intro,True.intro⟩⟩⟩,⟨sg41957,⟨sg41954,⟨sg41953,⟨sg41952,True.intro,True.intro⟩,True.intro⟩,⟨sg41956,⟨sg41955,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41960,⟨sg41959,⟨sg41958,True.intro,True.intro⟩,True.intro⟩,⟨sg41961,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_902All : degreeTree62_902.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41940,degreeTree62_900All,degreeTree62_901All⟩

lemma degreeTree62_903All : degreeTree62_903.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41973,⟨sg41968,⟨sg41965,⟨sg41964,⟨sg41963,True.intro,True.intro⟩,True.intro⟩,⟨sg41967,⟨sg41966,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41971,⟨sg41970,⟨sg41969,True.intro,True.intro⟩,True.intro⟩,⟨sg41972,True.intro,True.intro⟩⟩⟩,⟨sg41979,⟨sg41976,⟨sg41975,⟨sg41974,True.intro,True.intro⟩,True.intro⟩,⟨sg41978,⟨sg41977,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41982,⟨sg41981,⟨sg41980,True.intro,True.intro⟩,True.intro⟩,⟨sg41983,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_904All : degreeTree62_904.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41995,⟨sg41990,⟨sg41987,⟨sg41986,⟨sg41985,True.intro,True.intro⟩,True.intro⟩,⟨sg41989,⟨sg41988,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg41993,⟨sg41992,⟨sg41991,True.intro,True.intro⟩,True.intro⟩,⟨sg41994,True.intro,True.intro⟩⟩⟩,⟨sg42001,⟨sg41998,⟨sg41997,⟨sg41996,True.intro,True.intro⟩,True.intro⟩,⟨sg42000,⟨sg41999,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42004,⟨sg42003,⟨sg42002,True.intro,True.intro⟩,True.intro⟩,⟨sg42005,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_905All : degreeTree62_905.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41984,degreeTree62_903All,degreeTree62_904All⟩

lemma degreeTree62_906All : degreeTree62_906.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41962,degreeTree62_902All,degreeTree62_905All⟩

lemma degreeTree62_907All : degreeTree62_907.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41918,degreeTree62_899All,degreeTree62_906All⟩

lemma degreeTree62_908All : degreeTree62_908.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42017,⟨sg42012,⟨sg42009,⟨sg42008,⟨sg42007,True.intro,True.intro⟩,True.intro⟩,⟨sg42011,⟨sg42010,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42015,⟨sg42014,⟨sg42013,True.intro,True.intro⟩,True.intro⟩,⟨sg42016,True.intro,True.intro⟩⟩⟩,⟨sg42023,⟨sg42020,⟨sg42019,⟨sg42018,True.intro,True.intro⟩,True.intro⟩,⟨sg42022,⟨sg42021,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42026,⟨sg42025,⟨sg42024,True.intro,True.intro⟩,True.intro⟩,⟨sg42027,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_909All : degreeTree62_909.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42039,⟨sg42034,⟨sg42031,⟨sg42030,⟨sg42029,True.intro,True.intro⟩,True.intro⟩,⟨sg42033,⟨sg42032,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42037,⟨sg42036,⟨sg42035,True.intro,True.intro⟩,True.intro⟩,⟨sg42038,True.intro,True.intro⟩⟩⟩,⟨sg42045,⟨sg42042,⟨sg42041,⟨sg42040,True.intro,True.intro⟩,True.intro⟩,⟨sg42044,⟨sg42043,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42048,⟨sg42047,⟨sg42046,True.intro,True.intro⟩,True.intro⟩,⟨sg42049,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_910All : degreeTree62_910.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42028,degreeTree62_908All,degreeTree62_909All⟩

lemma degreeTree62_911All : degreeTree62_911.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42061,⟨sg42056,⟨sg42053,⟨sg42052,⟨sg42051,True.intro,True.intro⟩,True.intro⟩,⟨sg42055,⟨sg42054,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42059,⟨sg42058,⟨sg42057,True.intro,True.intro⟩,True.intro⟩,⟨sg42060,True.intro,True.intro⟩⟩⟩,⟨sg42067,⟨sg42064,⟨sg42063,⟨sg42062,True.intro,True.intro⟩,True.intro⟩,⟨sg42066,⟨sg42065,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42070,⟨sg42069,⟨sg42068,True.intro,True.intro⟩,True.intro⟩,⟨sg42071,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_912All : degreeTree62_912.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42083,⟨sg42078,⟨sg42075,⟨sg42074,⟨sg42073,True.intro,True.intro⟩,True.intro⟩,⟨sg42077,⟨sg42076,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42081,⟨sg42080,⟨sg42079,True.intro,True.intro⟩,True.intro⟩,⟨sg42082,True.intro,True.intro⟩⟩⟩,⟨sg42089,⟨sg42086,⟨sg42085,⟨sg42084,True.intro,True.intro⟩,True.intro⟩,⟨sg42088,⟨sg42087,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42092,⟨sg42091,⟨sg42090,True.intro,True.intro⟩,True.intro⟩,⟨sg42093,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_913All : degreeTree62_913.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42072,degreeTree62_911All,degreeTree62_912All⟩

lemma degreeTree62_914All : degreeTree62_914.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42050,degreeTree62_910All,degreeTree62_913All⟩

lemma degreeTree62_915All : degreeTree62_915.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42105,⟨sg42100,⟨sg42097,⟨sg42096,⟨sg42095,True.intro,True.intro⟩,True.intro⟩,⟨sg42099,⟨sg42098,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42103,⟨sg42102,⟨sg42101,True.intro,True.intro⟩,True.intro⟩,⟨sg42104,True.intro,True.intro⟩⟩⟩,⟨sg42111,⟨sg42108,⟨sg42107,⟨sg42106,True.intro,True.intro⟩,True.intro⟩,⟨sg42110,⟨sg42109,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42114,⟨sg42113,⟨sg42112,True.intro,True.intro⟩,True.intro⟩,⟨sg42115,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_916All : degreeTree62_916.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42127,⟨sg42122,⟨sg42119,⟨sg42118,⟨sg42117,True.intro,True.intro⟩,True.intro⟩,⟨sg42121,⟨sg42120,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42125,⟨sg42124,⟨sg42123,True.intro,True.intro⟩,True.intro⟩,⟨sg42126,True.intro,True.intro⟩⟩⟩,⟨sg42133,⟨sg42130,⟨sg42129,⟨sg42128,True.intro,True.intro⟩,True.intro⟩,⟨sg42132,⟨sg42131,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42136,⟨sg42135,⟨sg42134,True.intro,True.intro⟩,True.intro⟩,⟨sg42137,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_917All : degreeTree62_917.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42116,degreeTree62_915All,degreeTree62_916All⟩

lemma degreeTree62_918All : degreeTree62_918.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42149,⟨sg42144,⟨sg42141,⟨sg42140,⟨sg42139,True.intro,True.intro⟩,True.intro⟩,⟨sg42143,⟨sg42142,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42147,⟨sg42146,⟨sg42145,True.intro,True.intro⟩,True.intro⟩,⟨sg42148,True.intro,True.intro⟩⟩⟩,⟨sg42155,⟨sg42152,⟨sg42151,⟨sg42150,True.intro,True.intro⟩,True.intro⟩,⟨sg42154,⟨sg42153,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42158,⟨sg42157,⟨sg42156,True.intro,True.intro⟩,True.intro⟩,⟨sg42159,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_919All : degreeTree62_919.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42171,⟨sg42166,⟨sg42163,⟨sg42162,⟨sg42161,True.intro,True.intro⟩,True.intro⟩,⟨sg42165,⟨sg42164,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42169,⟨sg42168,⟨sg42167,True.intro,True.intro⟩,True.intro⟩,⟨sg42170,True.intro,True.intro⟩⟩⟩,⟨sg42176,⟨sg42174,⟨sg42173,⟨sg42172,True.intro,True.intro⟩,True.intro⟩,⟨sg42175,True.intro,True.intro⟩⟩,⟨sg42179,⟨sg42178,⟨sg42177,True.intro,True.intro⟩,True.intro⟩,⟨sg42180,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_920All : degreeTree62_920.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42160,degreeTree62_918All,degreeTree62_919All⟩

lemma degreeTree62_921All : degreeTree62_921.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42138,degreeTree62_917All,degreeTree62_920All⟩

lemma degreeTree62_922All : degreeTree62_922.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42094,degreeTree62_914All,degreeTree62_921All⟩

lemma degreeTree62_923All : degreeTree62_923.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42006,degreeTree62_907All,degreeTree62_922All⟩

lemma degreeTree62_924All : degreeTree62_924.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42192,⟨sg42187,⟨sg42184,⟨sg42183,⟨sg42182,True.intro,True.intro⟩,True.intro⟩,⟨sg42186,⟨sg42185,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42190,⟨sg42189,⟨sg42188,True.intro,True.intro⟩,True.intro⟩,⟨sg42191,True.intro,True.intro⟩⟩⟩,⟨sg42198,⟨sg42195,⟨sg42194,⟨sg42193,True.intro,True.intro⟩,True.intro⟩,⟨sg42197,⟨sg42196,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42201,⟨sg42200,⟨sg42199,True.intro,True.intro⟩,True.intro⟩,⟨sg42202,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_925All : degreeTree62_925.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42214,⟨sg42209,⟨sg42206,⟨sg42205,⟨sg42204,True.intro,True.intro⟩,True.intro⟩,⟨sg42208,⟨sg42207,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42212,⟨sg42211,⟨sg42210,True.intro,True.intro⟩,True.intro⟩,⟨sg42213,True.intro,True.intro⟩⟩⟩,⟨sg42220,⟨sg42217,⟨sg42216,⟨sg42215,True.intro,True.intro⟩,True.intro⟩,⟨sg42219,⟨sg42218,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42223,⟨sg42222,⟨sg42221,True.intro,True.intro⟩,True.intro⟩,⟨sg42224,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_926All : degreeTree62_926.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42203,degreeTree62_924All,degreeTree62_925All⟩

lemma degreeTree62_927All : degreeTree62_927.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42236,⟨sg42231,⟨sg42228,⟨sg42227,⟨sg42226,True.intro,True.intro⟩,True.intro⟩,⟨sg42230,⟨sg42229,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42234,⟨sg42233,⟨sg42232,True.intro,True.intro⟩,True.intro⟩,⟨sg42235,True.intro,True.intro⟩⟩⟩,⟨sg42242,⟨sg42239,⟨sg42238,⟨sg42237,True.intro,True.intro⟩,True.intro⟩,⟨sg42241,⟨sg42240,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42245,⟨sg42244,⟨sg42243,True.intro,True.intro⟩,True.intro⟩,⟨sg42246,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_928All : degreeTree62_928.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42258,⟨sg42253,⟨sg42250,⟨sg42249,⟨sg42248,True.intro,True.intro⟩,True.intro⟩,⟨sg42252,⟨sg42251,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42256,⟨sg42255,⟨sg42254,True.intro,True.intro⟩,True.intro⟩,⟨sg42257,True.intro,True.intro⟩⟩⟩,⟨sg42264,⟨sg42261,⟨sg42260,⟨sg42259,True.intro,True.intro⟩,True.intro⟩,⟨sg42263,⟨sg42262,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42267,⟨sg42266,⟨sg42265,True.intro,True.intro⟩,True.intro⟩,⟨sg42268,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_929All : degreeTree62_929.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42247,degreeTree62_927All,degreeTree62_928All⟩

lemma degreeTree62_930All : degreeTree62_930.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42225,degreeTree62_926All,degreeTree62_929All⟩

lemma degreeTree62_931All : degreeTree62_931.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42280,⟨sg42275,⟨sg42272,⟨sg42271,⟨sg42270,True.intro,True.intro⟩,True.intro⟩,⟨sg42274,⟨sg42273,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42278,⟨sg42277,⟨sg42276,True.intro,True.intro⟩,True.intro⟩,⟨sg42279,True.intro,True.intro⟩⟩⟩,⟨sg42286,⟨sg42283,⟨sg42282,⟨sg42281,True.intro,True.intro⟩,True.intro⟩,⟨sg42285,⟨sg42284,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42289,⟨sg42288,⟨sg42287,True.intro,True.intro⟩,True.intro⟩,⟨sg42290,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_932All : degreeTree62_932.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42302,⟨sg42297,⟨sg42294,⟨sg42293,⟨sg42292,True.intro,True.intro⟩,True.intro⟩,⟨sg42296,⟨sg42295,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42300,⟨sg42299,⟨sg42298,True.intro,True.intro⟩,True.intro⟩,⟨sg42301,True.intro,True.intro⟩⟩⟩,⟨sg42308,⟨sg42305,⟨sg42304,⟨sg42303,True.intro,True.intro⟩,True.intro⟩,⟨sg42307,⟨sg42306,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42311,⟨sg42310,⟨sg42309,True.intro,True.intro⟩,True.intro⟩,⟨sg42312,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_933All : degreeTree62_933.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42291,degreeTree62_931All,degreeTree62_932All⟩

lemma degreeTree62_934All : degreeTree62_934.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42324,⟨sg42319,⟨sg42316,⟨sg42315,⟨sg42314,True.intro,True.intro⟩,True.intro⟩,⟨sg42318,⟨sg42317,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42322,⟨sg42321,⟨sg42320,True.intro,True.intro⟩,True.intro⟩,⟨sg42323,True.intro,True.intro⟩⟩⟩,⟨sg42330,⟨sg42327,⟨sg42326,⟨sg42325,True.intro,True.intro⟩,True.intro⟩,⟨sg42329,⟨sg42328,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42333,⟨sg42332,⟨sg42331,True.intro,True.intro⟩,True.intro⟩,⟨sg42334,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_935All : degreeTree62_935.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42346,⟨sg42341,⟨sg42338,⟨sg42337,⟨sg42336,True.intro,True.intro⟩,True.intro⟩,⟨sg42340,⟨sg42339,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42344,⟨sg42343,⟨sg42342,True.intro,True.intro⟩,True.intro⟩,⟨sg42345,True.intro,True.intro⟩⟩⟩,⟨sg42352,⟨sg42349,⟨sg42348,⟨sg42347,True.intro,True.intro⟩,True.intro⟩,⟨sg42351,⟨sg42350,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42355,⟨sg42354,⟨sg42353,True.intro,True.intro⟩,True.intro⟩,⟨sg42356,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_936All : degreeTree62_936.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42335,degreeTree62_934All,degreeTree62_935All⟩

lemma degreeTree62_937All : degreeTree62_937.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42313,degreeTree62_933All,degreeTree62_936All⟩

lemma degreeTree62_938All : degreeTree62_938.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42269,degreeTree62_930All,degreeTree62_937All⟩

lemma degreeTree62_939All : degreeTree62_939.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42368,⟨sg42363,⟨sg42360,⟨sg42359,⟨sg42358,True.intro,True.intro⟩,True.intro⟩,⟨sg42362,⟨sg42361,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42366,⟨sg42365,⟨sg42364,True.intro,True.intro⟩,True.intro⟩,⟨sg42367,True.intro,True.intro⟩⟩⟩,⟨sg42374,⟨sg42371,⟨sg42370,⟨sg42369,True.intro,True.intro⟩,True.intro⟩,⟨sg42373,⟨sg42372,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42377,⟨sg42376,⟨sg42375,True.intro,True.intro⟩,True.intro⟩,⟨sg42378,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_940All : degreeTree62_940.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42390,⟨sg42385,⟨sg42382,⟨sg42381,⟨sg42380,True.intro,True.intro⟩,True.intro⟩,⟨sg42384,⟨sg42383,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42388,⟨sg42387,⟨sg42386,True.intro,True.intro⟩,True.intro⟩,⟨sg42389,True.intro,True.intro⟩⟩⟩,⟨sg42396,⟨sg42393,⟨sg42392,⟨sg42391,True.intro,True.intro⟩,True.intro⟩,⟨sg42395,⟨sg42394,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42399,⟨sg42398,⟨sg42397,True.intro,True.intro⟩,True.intro⟩,⟨sg42400,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_941All : degreeTree62_941.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42379,degreeTree62_939All,degreeTree62_940All⟩

lemma degreeTree62_942All : degreeTree62_942.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42412,⟨sg42407,⟨sg42404,⟨sg42403,⟨sg42402,True.intro,True.intro⟩,True.intro⟩,⟨sg42406,⟨sg42405,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42410,⟨sg42409,⟨sg42408,True.intro,True.intro⟩,True.intro⟩,⟨sg42411,True.intro,True.intro⟩⟩⟩,⟨sg42418,⟨sg42415,⟨sg42414,⟨sg42413,True.intro,True.intro⟩,True.intro⟩,⟨sg42417,⟨sg42416,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42421,⟨sg42420,⟨sg42419,True.intro,True.intro⟩,True.intro⟩,⟨sg42422,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_943All : degreeTree62_943.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42434,⟨sg42429,⟨sg42426,⟨sg42425,⟨sg42424,True.intro,True.intro⟩,True.intro⟩,⟨sg42428,⟨sg42427,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42432,⟨sg42431,⟨sg42430,True.intro,True.intro⟩,True.intro⟩,⟨sg42433,True.intro,True.intro⟩⟩⟩,⟨sg42440,⟨sg42437,⟨sg42436,⟨sg42435,True.intro,True.intro⟩,True.intro⟩,⟨sg42439,⟨sg42438,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42443,⟨sg42442,⟨sg42441,True.intro,True.intro⟩,True.intro⟩,⟨sg42444,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_944All : degreeTree62_944.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42423,degreeTree62_942All,degreeTree62_943All⟩

lemma degreeTree62_945All : degreeTree62_945.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42401,degreeTree62_941All,degreeTree62_944All⟩

lemma degreeTree62_946All : degreeTree62_946.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42456,⟨sg42451,⟨sg42448,⟨sg42447,⟨sg42446,True.intro,True.intro⟩,True.intro⟩,⟨sg42450,⟨sg42449,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42454,⟨sg42453,⟨sg42452,True.intro,True.intro⟩,True.intro⟩,⟨sg42455,True.intro,True.intro⟩⟩⟩,⟨sg42462,⟨sg42459,⟨sg42458,⟨sg42457,True.intro,True.intro⟩,True.intro⟩,⟨sg42461,⟨sg42460,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42465,⟨sg42464,⟨sg42463,True.intro,True.intro⟩,True.intro⟩,⟨sg42466,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_947All : degreeTree62_947.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42478,⟨sg42473,⟨sg42470,⟨sg42469,⟨sg42468,True.intro,True.intro⟩,True.intro⟩,⟨sg42472,⟨sg42471,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42476,⟨sg42475,⟨sg42474,True.intro,True.intro⟩,True.intro⟩,⟨sg42477,True.intro,True.intro⟩⟩⟩,⟨sg42484,⟨sg42481,⟨sg42480,⟨sg42479,True.intro,True.intro⟩,True.intro⟩,⟨sg42483,⟨sg42482,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42487,⟨sg42486,⟨sg42485,True.intro,True.intro⟩,True.intro⟩,⟨sg42488,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_948All : degreeTree62_948.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42467,degreeTree62_946All,degreeTree62_947All⟩

lemma degreeTree62_949All : degreeTree62_949.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42500,⟨sg42495,⟨sg42492,⟨sg42491,⟨sg42490,True.intro,True.intro⟩,True.intro⟩,⟨sg42494,⟨sg42493,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42498,⟨sg42497,⟨sg42496,True.intro,True.intro⟩,True.intro⟩,⟨sg42499,True.intro,True.intro⟩⟩⟩,⟨sg42506,⟨sg42503,⟨sg42502,⟨sg42501,True.intro,True.intro⟩,True.intro⟩,⟨sg42505,⟨sg42504,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42509,⟨sg42508,⟨sg42507,True.intro,True.intro⟩,True.intro⟩,⟨sg42510,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_950All : degreeTree62_950.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42522,⟨sg42517,⟨sg42514,⟨sg42513,⟨sg42512,True.intro,True.intro⟩,True.intro⟩,⟨sg42516,⟨sg42515,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42520,⟨sg42519,⟨sg42518,True.intro,True.intro⟩,True.intro⟩,⟨sg42521,True.intro,True.intro⟩⟩⟩,⟨sg42527,⟨sg42525,⟨sg42524,⟨sg42523,True.intro,True.intro⟩,True.intro⟩,⟨sg42526,True.intro,True.intro⟩⟩,⟨sg42530,⟨sg42529,⟨sg42528,True.intro,True.intro⟩,True.intro⟩,⟨sg42531,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_951All : degreeTree62_951.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42511,degreeTree62_949All,degreeTree62_950All⟩

lemma degreeTree62_952All : degreeTree62_952.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42489,degreeTree62_948All,degreeTree62_951All⟩

lemma degreeTree62_953All : degreeTree62_953.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42445,degreeTree62_945All,degreeTree62_952All⟩

lemma degreeTree62_954All : degreeTree62_954.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42357,degreeTree62_938All,degreeTree62_953All⟩

lemma degreeTree62_955All : degreeTree62_955.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42181,degreeTree62_923All,degreeTree62_954All⟩

lemma degreeTree62_956All : degreeTree62_956.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42543,⟨sg42538,⟨sg42535,⟨sg42534,⟨sg42533,True.intro,True.intro⟩,True.intro⟩,⟨sg42537,⟨sg42536,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42541,⟨sg42540,⟨sg42539,True.intro,True.intro⟩,True.intro⟩,⟨sg42542,True.intro,True.intro⟩⟩⟩,⟨sg42549,⟨sg42546,⟨sg42545,⟨sg42544,True.intro,True.intro⟩,True.intro⟩,⟨sg42548,⟨sg42547,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42552,⟨sg42551,⟨sg42550,True.intro,True.intro⟩,True.intro⟩,⟨sg42553,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_957All : degreeTree62_957.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42565,⟨sg42560,⟨sg42557,⟨sg42556,⟨sg42555,True.intro,True.intro⟩,True.intro⟩,⟨sg42559,⟨sg42558,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42563,⟨sg42562,⟨sg42561,True.intro,True.intro⟩,True.intro⟩,⟨sg42564,True.intro,True.intro⟩⟩⟩,⟨sg42571,⟨sg42568,⟨sg42567,⟨sg42566,True.intro,True.intro⟩,True.intro⟩,⟨sg42570,⟨sg42569,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42574,⟨sg42573,⟨sg42572,True.intro,True.intro⟩,True.intro⟩,⟨sg42575,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_958All : degreeTree62_958.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42554,degreeTree62_956All,degreeTree62_957All⟩

lemma degreeTree62_959All : degreeTree62_959.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42587,⟨sg42582,⟨sg42579,⟨sg42578,⟨sg42577,True.intro,True.intro⟩,True.intro⟩,⟨sg42581,⟨sg42580,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42585,⟨sg42584,⟨sg42583,True.intro,True.intro⟩,True.intro⟩,⟨sg42586,True.intro,True.intro⟩⟩⟩,⟨sg42593,⟨sg42590,⟨sg42589,⟨sg42588,True.intro,True.intro⟩,True.intro⟩,⟨sg42592,⟨sg42591,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42596,⟨sg42595,⟨sg42594,True.intro,True.intro⟩,True.intro⟩,⟨sg42597,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_960All : degreeTree62_960.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42609,⟨sg42604,⟨sg42601,⟨sg42600,⟨sg42599,True.intro,True.intro⟩,True.intro⟩,⟨sg42603,⟨sg42602,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42607,⟨sg42606,⟨sg42605,True.intro,True.intro⟩,True.intro⟩,⟨sg42608,True.intro,True.intro⟩⟩⟩,⟨sg42615,⟨sg42612,⟨sg42611,⟨sg42610,True.intro,True.intro⟩,True.intro⟩,⟨sg42614,⟨sg42613,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42618,⟨sg42617,⟨sg42616,True.intro,True.intro⟩,True.intro⟩,⟨sg42619,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_961All : degreeTree62_961.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42598,degreeTree62_959All,degreeTree62_960All⟩

lemma degreeTree62_962All : degreeTree62_962.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42576,degreeTree62_958All,degreeTree62_961All⟩

lemma degreeTree62_963All : degreeTree62_963.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42631,⟨sg42626,⟨sg42623,⟨sg42622,⟨sg42621,True.intro,True.intro⟩,True.intro⟩,⟨sg42625,⟨sg42624,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42629,⟨sg42628,⟨sg42627,True.intro,True.intro⟩,True.intro⟩,⟨sg42630,True.intro,True.intro⟩⟩⟩,⟨sg42637,⟨sg42634,⟨sg42633,⟨sg42632,True.intro,True.intro⟩,True.intro⟩,⟨sg42636,⟨sg42635,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42640,⟨sg42639,⟨sg42638,True.intro,True.intro⟩,True.intro⟩,⟨sg42641,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_964All : degreeTree62_964.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42653,⟨sg42648,⟨sg42645,⟨sg42644,⟨sg42643,True.intro,True.intro⟩,True.intro⟩,⟨sg42647,⟨sg42646,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42651,⟨sg42650,⟨sg42649,True.intro,True.intro⟩,True.intro⟩,⟨sg42652,True.intro,True.intro⟩⟩⟩,⟨sg42659,⟨sg42656,⟨sg42655,⟨sg42654,True.intro,True.intro⟩,True.intro⟩,⟨sg42658,⟨sg42657,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42662,⟨sg42661,⟨sg42660,True.intro,True.intro⟩,True.intro⟩,⟨sg42663,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_965All : degreeTree62_965.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42642,degreeTree62_963All,degreeTree62_964All⟩

lemma degreeTree62_966All : degreeTree62_966.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42675,⟨sg42670,⟨sg42667,⟨sg42666,⟨sg42665,True.intro,True.intro⟩,True.intro⟩,⟨sg42669,⟨sg42668,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42673,⟨sg42672,⟨sg42671,True.intro,True.intro⟩,True.intro⟩,⟨sg42674,True.intro,True.intro⟩⟩⟩,⟨sg42681,⟨sg42678,⟨sg42677,⟨sg42676,True.intro,True.intro⟩,True.intro⟩,⟨sg42680,⟨sg42679,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42684,⟨sg42683,⟨sg42682,True.intro,True.intro⟩,True.intro⟩,⟨sg42685,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_967All : degreeTree62_967.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42697,⟨sg42692,⟨sg42689,⟨sg42688,⟨sg42687,True.intro,True.intro⟩,True.intro⟩,⟨sg42691,⟨sg42690,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42695,⟨sg42694,⟨sg42693,True.intro,True.intro⟩,True.intro⟩,⟨sg42696,True.intro,True.intro⟩⟩⟩,⟨sg42703,⟨sg42700,⟨sg42699,⟨sg42698,True.intro,True.intro⟩,True.intro⟩,⟨sg42702,⟨sg42701,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42706,⟨sg42705,⟨sg42704,True.intro,True.intro⟩,True.intro⟩,⟨sg42707,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_968All : degreeTree62_968.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42686,degreeTree62_966All,degreeTree62_967All⟩

lemma degreeTree62_969All : degreeTree62_969.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42664,degreeTree62_965All,degreeTree62_968All⟩

lemma degreeTree62_970All : degreeTree62_970.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42620,degreeTree62_962All,degreeTree62_969All⟩

lemma degreeTree62_971All : degreeTree62_971.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42719,⟨sg42714,⟨sg42711,⟨sg42710,⟨sg42709,True.intro,True.intro⟩,True.intro⟩,⟨sg42713,⟨sg42712,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42717,⟨sg42716,⟨sg42715,True.intro,True.intro⟩,True.intro⟩,⟨sg42718,True.intro,True.intro⟩⟩⟩,⟨sg42725,⟨sg42722,⟨sg42721,⟨sg42720,True.intro,True.intro⟩,True.intro⟩,⟨sg42724,⟨sg42723,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42728,⟨sg42727,⟨sg42726,True.intro,True.intro⟩,True.intro⟩,⟨sg42729,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_972All : degreeTree62_972.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42741,⟨sg42736,⟨sg42733,⟨sg42732,⟨sg42731,True.intro,True.intro⟩,True.intro⟩,⟨sg42735,⟨sg42734,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42739,⟨sg42738,⟨sg42737,True.intro,True.intro⟩,True.intro⟩,⟨sg42740,True.intro,True.intro⟩⟩⟩,⟨sg42747,⟨sg42744,⟨sg42743,⟨sg42742,True.intro,True.intro⟩,True.intro⟩,⟨sg42746,⟨sg42745,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42750,⟨sg42749,⟨sg42748,True.intro,True.intro⟩,True.intro⟩,⟨sg42751,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_973All : degreeTree62_973.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42730,degreeTree62_971All,degreeTree62_972All⟩

lemma degreeTree62_974All : degreeTree62_974.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42763,⟨sg42758,⟨sg42755,⟨sg42754,⟨sg42753,True.intro,True.intro⟩,True.intro⟩,⟨sg42757,⟨sg42756,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42761,⟨sg42760,⟨sg42759,True.intro,True.intro⟩,True.intro⟩,⟨sg42762,True.intro,True.intro⟩⟩⟩,⟨sg42769,⟨sg42766,⟨sg42765,⟨sg42764,True.intro,True.intro⟩,True.intro⟩,⟨sg42768,⟨sg42767,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42772,⟨sg42771,⟨sg42770,True.intro,True.intro⟩,True.intro⟩,⟨sg42773,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_975All : degreeTree62_975.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42785,⟨sg42780,⟨sg42777,⟨sg42776,⟨sg42775,True.intro,True.intro⟩,True.intro⟩,⟨sg42779,⟨sg42778,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42783,⟨sg42782,⟨sg42781,True.intro,True.intro⟩,True.intro⟩,⟨sg42784,True.intro,True.intro⟩⟩⟩,⟨sg42791,⟨sg42788,⟨sg42787,⟨sg42786,True.intro,True.intro⟩,True.intro⟩,⟨sg42790,⟨sg42789,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42794,⟨sg42793,⟨sg42792,True.intro,True.intro⟩,True.intro⟩,⟨sg42795,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_976All : degreeTree62_976.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42774,degreeTree62_974All,degreeTree62_975All⟩

lemma degreeTree62_977All : degreeTree62_977.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42752,degreeTree62_973All,degreeTree62_976All⟩

lemma degreeTree62_978All : degreeTree62_978.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42807,⟨sg42802,⟨sg42799,⟨sg42798,⟨sg42797,True.intro,True.intro⟩,True.intro⟩,⟨sg42801,⟨sg42800,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42805,⟨sg42804,⟨sg42803,True.intro,True.intro⟩,True.intro⟩,⟨sg42806,True.intro,True.intro⟩⟩⟩,⟨sg42813,⟨sg42810,⟨sg42809,⟨sg42808,True.intro,True.intro⟩,True.intro⟩,⟨sg42812,⟨sg42811,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42816,⟨sg42815,⟨sg42814,True.intro,True.intro⟩,True.intro⟩,⟨sg42817,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_979All : degreeTree62_979.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42829,⟨sg42824,⟨sg42821,⟨sg42820,⟨sg42819,True.intro,True.intro⟩,True.intro⟩,⟨sg42823,⟨sg42822,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42827,⟨sg42826,⟨sg42825,True.intro,True.intro⟩,True.intro⟩,⟨sg42828,True.intro,True.intro⟩⟩⟩,⟨sg42835,⟨sg42832,⟨sg42831,⟨sg42830,True.intro,True.intro⟩,True.intro⟩,⟨sg42834,⟨sg42833,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42838,⟨sg42837,⟨sg42836,True.intro,True.intro⟩,True.intro⟩,⟨sg42839,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_980All : degreeTree62_980.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42818,degreeTree62_978All,degreeTree62_979All⟩

lemma degreeTree62_981All : degreeTree62_981.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42851,⟨sg42846,⟨sg42843,⟨sg42842,⟨sg42841,True.intro,True.intro⟩,True.intro⟩,⟨sg42845,⟨sg42844,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42849,⟨sg42848,⟨sg42847,True.intro,True.intro⟩,True.intro⟩,⟨sg42850,True.intro,True.intro⟩⟩⟩,⟨sg42857,⟨sg42854,⟨sg42853,⟨sg42852,True.intro,True.intro⟩,True.intro⟩,⟨sg42856,⟨sg42855,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42860,⟨sg42859,⟨sg42858,True.intro,True.intro⟩,True.intro⟩,⟨sg42861,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_982All : degreeTree62_982.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42873,⟨sg42868,⟨sg42865,⟨sg42864,⟨sg42863,True.intro,True.intro⟩,True.intro⟩,⟨sg42867,⟨sg42866,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42871,⟨sg42870,⟨sg42869,True.intro,True.intro⟩,True.intro⟩,⟨sg42872,True.intro,True.intro⟩⟩⟩,⟨sg42878,⟨sg42876,⟨sg42875,⟨sg42874,True.intro,True.intro⟩,True.intro⟩,⟨sg42877,True.intro,True.intro⟩⟩,⟨sg42881,⟨sg42880,⟨sg42879,True.intro,True.intro⟩,True.intro⟩,⟨sg42882,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_983All : degreeTree62_983.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42862,degreeTree62_981All,degreeTree62_982All⟩

lemma degreeTree62_984All : degreeTree62_984.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42840,degreeTree62_980All,degreeTree62_983All⟩

lemma degreeTree62_985All : degreeTree62_985.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42796,degreeTree62_977All,degreeTree62_984All⟩

lemma degreeTree62_986All : degreeTree62_986.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42708,degreeTree62_970All,degreeTree62_985All⟩

lemma degreeTree62_987All : degreeTree62_987.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42894,⟨sg42889,⟨sg42886,⟨sg42885,⟨sg42884,True.intro,True.intro⟩,True.intro⟩,⟨sg42888,⟨sg42887,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42892,⟨sg42891,⟨sg42890,True.intro,True.intro⟩,True.intro⟩,⟨sg42893,True.intro,True.intro⟩⟩⟩,⟨sg42900,⟨sg42897,⟨sg42896,⟨sg42895,True.intro,True.intro⟩,True.intro⟩,⟨sg42899,⟨sg42898,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42903,⟨sg42902,⟨sg42901,True.intro,True.intro⟩,True.intro⟩,⟨sg42904,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_988All : degreeTree62_988.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42916,⟨sg42911,⟨sg42908,⟨sg42907,⟨sg42906,True.intro,True.intro⟩,True.intro⟩,⟨sg42910,⟨sg42909,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42914,⟨sg42913,⟨sg42912,True.intro,True.intro⟩,True.intro⟩,⟨sg42915,True.intro,True.intro⟩⟩⟩,⟨sg42922,⟨sg42919,⟨sg42918,⟨sg42917,True.intro,True.intro⟩,True.intro⟩,⟨sg42921,⟨sg42920,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42925,⟨sg42924,⟨sg42923,True.intro,True.intro⟩,True.intro⟩,⟨sg42926,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_989All : degreeTree62_989.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42905,degreeTree62_987All,degreeTree62_988All⟩

lemma degreeTree62_990All : degreeTree62_990.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42938,⟨sg42933,⟨sg42930,⟨sg42929,⟨sg42928,True.intro,True.intro⟩,True.intro⟩,⟨sg42932,⟨sg42931,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42936,⟨sg42935,⟨sg42934,True.intro,True.intro⟩,True.intro⟩,⟨sg42937,True.intro,True.intro⟩⟩⟩,⟨sg42944,⟨sg42941,⟨sg42940,⟨sg42939,True.intro,True.intro⟩,True.intro⟩,⟨sg42943,⟨sg42942,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42947,⟨sg42946,⟨sg42945,True.intro,True.intro⟩,True.intro⟩,⟨sg42948,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_991All : degreeTree62_991.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42960,⟨sg42955,⟨sg42952,⟨sg42951,⟨sg42950,True.intro,True.intro⟩,True.intro⟩,⟨sg42954,⟨sg42953,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42958,⟨sg42957,⟨sg42956,True.intro,True.intro⟩,True.intro⟩,⟨sg42959,True.intro,True.intro⟩⟩⟩,⟨sg42966,⟨sg42963,⟨sg42962,⟨sg42961,True.intro,True.intro⟩,True.intro⟩,⟨sg42965,⟨sg42964,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42969,⟨sg42968,⟨sg42967,True.intro,True.intro⟩,True.intro⟩,⟨sg42970,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_992All : degreeTree62_992.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42949,degreeTree62_990All,degreeTree62_991All⟩

lemma degreeTree62_993All : degreeTree62_993.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42927,degreeTree62_989All,degreeTree62_992All⟩

lemma degreeTree62_994All : degreeTree62_994.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42982,⟨sg42977,⟨sg42974,⟨sg42973,⟨sg42972,True.intro,True.intro⟩,True.intro⟩,⟨sg42976,⟨sg42975,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42980,⟨sg42979,⟨sg42978,True.intro,True.intro⟩,True.intro⟩,⟨sg42981,True.intro,True.intro⟩⟩⟩,⟨sg42988,⟨sg42985,⟨sg42984,⟨sg42983,True.intro,True.intro⟩,True.intro⟩,⟨sg42987,⟨sg42986,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg42991,⟨sg42990,⟨sg42989,True.intro,True.intro⟩,True.intro⟩,⟨sg42992,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_995All : degreeTree62_995.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43004,⟨sg42999,⟨sg42996,⟨sg42995,⟨sg42994,True.intro,True.intro⟩,True.intro⟩,⟨sg42998,⟨sg42997,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43002,⟨sg43001,⟨sg43000,True.intro,True.intro⟩,True.intro⟩,⟨sg43003,True.intro,True.intro⟩⟩⟩,⟨sg43010,⟨sg43007,⟨sg43006,⟨sg43005,True.intro,True.intro⟩,True.intro⟩,⟨sg43009,⟨sg43008,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43013,⟨sg43012,⟨sg43011,True.intro,True.intro⟩,True.intro⟩,⟨sg43014,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_996All : degreeTree62_996.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42993,degreeTree62_994All,degreeTree62_995All⟩

lemma degreeTree62_997All : degreeTree62_997.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43026,⟨sg43021,⟨sg43018,⟨sg43017,⟨sg43016,True.intro,True.intro⟩,True.intro⟩,⟨sg43020,⟨sg43019,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43024,⟨sg43023,⟨sg43022,True.intro,True.intro⟩,True.intro⟩,⟨sg43025,True.intro,True.intro⟩⟩⟩,⟨sg43032,⟨sg43029,⟨sg43028,⟨sg43027,True.intro,True.intro⟩,True.intro⟩,⟨sg43031,⟨sg43030,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43035,⟨sg43034,⟨sg43033,True.intro,True.intro⟩,True.intro⟩,⟨sg43036,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_998All : degreeTree62_998.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43048,⟨sg43043,⟨sg43040,⟨sg43039,⟨sg43038,True.intro,True.intro⟩,True.intro⟩,⟨sg43042,⟨sg43041,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43046,⟨sg43045,⟨sg43044,True.intro,True.intro⟩,True.intro⟩,⟨sg43047,True.intro,True.intro⟩⟩⟩,⟨sg43053,⟨sg43051,⟨sg43050,⟨sg43049,True.intro,True.intro⟩,True.intro⟩,⟨sg43052,True.intro,True.intro⟩⟩,⟨sg43056,⟨sg43055,⟨sg43054,True.intro,True.intro⟩,True.intro⟩,⟨sg43057,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_999All : degreeTree62_999.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43037,degreeTree62_997All,degreeTree62_998All⟩

lemma degreeTree62_1000All : degreeTree62_1000.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43015,degreeTree62_996All,degreeTree62_999All⟩

lemma degreeTree62_1001All : degreeTree62_1001.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42971,degreeTree62_993All,degreeTree62_1000All⟩

lemma degreeTree62_1002All : degreeTree62_1002.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43069,⟨sg43064,⟨sg43061,⟨sg43060,⟨sg43059,True.intro,True.intro⟩,True.intro⟩,⟨sg43063,⟨sg43062,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43067,⟨sg43066,⟨sg43065,True.intro,True.intro⟩,True.intro⟩,⟨sg43068,True.intro,True.intro⟩⟩⟩,⟨sg43075,⟨sg43072,⟨sg43071,⟨sg43070,True.intro,True.intro⟩,True.intro⟩,⟨sg43074,⟨sg43073,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43078,⟨sg43077,⟨sg43076,True.intro,True.intro⟩,True.intro⟩,⟨sg43079,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1003All : degreeTree62_1003.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43091,⟨sg43086,⟨sg43083,⟨sg43082,⟨sg43081,True.intro,True.intro⟩,True.intro⟩,⟨sg43085,⟨sg43084,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43089,⟨sg43088,⟨sg43087,True.intro,True.intro⟩,True.intro⟩,⟨sg43090,True.intro,True.intro⟩⟩⟩,⟨sg43097,⟨sg43094,⟨sg43093,⟨sg43092,True.intro,True.intro⟩,True.intro⟩,⟨sg43096,⟨sg43095,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43100,⟨sg43099,⟨sg43098,True.intro,True.intro⟩,True.intro⟩,⟨sg43101,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1004All : degreeTree62_1004.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43080,degreeTree62_1002All,degreeTree62_1003All⟩

lemma degreeTree62_1005All : degreeTree62_1005.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43113,⟨sg43108,⟨sg43105,⟨sg43104,⟨sg43103,True.intro,True.intro⟩,True.intro⟩,⟨sg43107,⟨sg43106,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43111,⟨sg43110,⟨sg43109,True.intro,True.intro⟩,True.intro⟩,⟨sg43112,True.intro,True.intro⟩⟩⟩,⟨sg43119,⟨sg43116,⟨sg43115,⟨sg43114,True.intro,True.intro⟩,True.intro⟩,⟨sg43118,⟨sg43117,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43122,⟨sg43121,⟨sg43120,True.intro,True.intro⟩,True.intro⟩,⟨sg43123,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1006All : degreeTree62_1006.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43135,⟨sg43130,⟨sg43127,⟨sg43126,⟨sg43125,True.intro,True.intro⟩,True.intro⟩,⟨sg43129,⟨sg43128,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43133,⟨sg43132,⟨sg43131,True.intro,True.intro⟩,True.intro⟩,⟨sg43134,True.intro,True.intro⟩⟩⟩,⟨sg43141,⟨sg43138,⟨sg43137,⟨sg43136,True.intro,True.intro⟩,True.intro⟩,⟨sg43140,⟨sg43139,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43144,⟨sg43143,⟨sg43142,True.intro,True.intro⟩,True.intro⟩,⟨sg43145,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1007All : degreeTree62_1007.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43124,degreeTree62_1005All,degreeTree62_1006All⟩

lemma degreeTree62_1008All : degreeTree62_1008.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43102,degreeTree62_1004All,degreeTree62_1007All⟩

lemma degreeTree62_1009All : degreeTree62_1009.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43157,⟨sg43152,⟨sg43149,⟨sg43148,⟨sg43147,True.intro,True.intro⟩,True.intro⟩,⟨sg43151,⟨sg43150,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43155,⟨sg43154,⟨sg43153,True.intro,True.intro⟩,True.intro⟩,⟨sg43156,True.intro,True.intro⟩⟩⟩,⟨sg43163,⟨sg43160,⟨sg43159,⟨sg43158,True.intro,True.intro⟩,True.intro⟩,⟨sg43162,⟨sg43161,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43166,⟨sg43165,⟨sg43164,True.intro,True.intro⟩,True.intro⟩,⟨sg43167,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1010All : degreeTree62_1010.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43179,⟨sg43174,⟨sg43171,⟨sg43170,⟨sg43169,True.intro,True.intro⟩,True.intro⟩,⟨sg43173,⟨sg43172,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43177,⟨sg43176,⟨sg43175,True.intro,True.intro⟩,True.intro⟩,⟨sg43178,True.intro,True.intro⟩⟩⟩,⟨sg43185,⟨sg43182,⟨sg43181,⟨sg43180,True.intro,True.intro⟩,True.intro⟩,⟨sg43184,⟨sg43183,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43188,⟨sg43187,⟨sg43186,True.intro,True.intro⟩,True.intro⟩,⟨sg43189,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1011All : degreeTree62_1011.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43168,degreeTree62_1009All,degreeTree62_1010All⟩

lemma degreeTree62_1012All : degreeTree62_1012.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43201,⟨sg43196,⟨sg43193,⟨sg43192,⟨sg43191,True.intro,True.intro⟩,True.intro⟩,⟨sg43195,⟨sg43194,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43199,⟨sg43198,⟨sg43197,True.intro,True.intro⟩,True.intro⟩,⟨sg43200,True.intro,True.intro⟩⟩⟩,⟨sg43207,⟨sg43204,⟨sg43203,⟨sg43202,True.intro,True.intro⟩,True.intro⟩,⟨sg43206,⟨sg43205,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43210,⟨sg43209,⟨sg43208,True.intro,True.intro⟩,True.intro⟩,⟨sg43211,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1013All : degreeTree62_1013.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43223,⟨sg43218,⟨sg43215,⟨sg43214,⟨sg43213,True.intro,True.intro⟩,True.intro⟩,⟨sg43217,⟨sg43216,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg43221,⟨sg43220,⟨sg43219,True.intro,True.intro⟩,True.intro⟩,⟨sg43222,True.intro,True.intro⟩⟩⟩,⟨sg43228,⟨sg43226,⟨sg43225,⟨sg43224,True.intro,True.intro⟩,True.intro⟩,⟨sg43227,True.intro,True.intro⟩⟩,⟨sg43231,⟨sg43230,⟨sg43229,True.intro,True.intro⟩,True.intro⟩,⟨sg43232,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree62_1014All : degreeTree62_1014.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43212,degreeTree62_1012All,degreeTree62_1013All⟩

lemma degreeTree62_1015All : degreeTree62_1015.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43190,degreeTree62_1011All,degreeTree62_1014All⟩

lemma degreeTree62_1016All : degreeTree62_1016.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43146,degreeTree62_1008All,degreeTree62_1015All⟩

lemma degreeTree62_1017All : degreeTree62_1017.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg43058,degreeTree62_1001All,degreeTree62_1016All⟩

lemma degreeTree62_1018All : degreeTree62_1018.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42883,degreeTree62_986All,degreeTree62_1017All⟩

lemma degreeTree62_1019All : degreeTree62_1019.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg42532,degreeTree62_955All,degreeTree62_1018All⟩

lemma degreeTree62_1020All : degreeTree62_1020.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg41830,degreeTree62_892All,degreeTree62_1019All⟩

lemma degreeTree62_1021All : degreeTree62_1021.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg40426,degreeTree62_765All,degreeTree62_1020All⟩

lemma degreeTree62_1022All : degreeTree62_1022.All (RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg37619,degreeTree62_510All,degreeTree62_1021All⟩

lemma degreeTreeAll62 : degreeTree62.All
    (fun rs => SquareOccurs (candidate 8 6 1) (rowDiagram rs)) := by
  have hp : rowDiagram [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] = candidate 8 6 1 := rowDiagram_candidate (M := 8) (b := 6) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree62_1022All

end UniversalTensorSquare
end
end

end OAI
