import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData26
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes31
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32

namespace OAI

/-! Degree Tree Proof 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree26_0All : degreeTree26_0.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg12979,⟨sg12975,⟨sg12973,⟨sg12972,⟨sg12971,True.intro,True.intro⟩,True.intro⟩,⟨sg12974,True.intro,True.intro⟩⟩,⟨sg12977,⟨sg12976,True.intro,True.intro⟩,⟨sg12978,True.intro,True.intro⟩⟩⟩,⟨sg12983,⟨sg12981,⟨sg12980,True.intro,True.intro⟩,⟨sg12982,True.intro,True.intro⟩⟩,⟨sg12985,⟨sg12984,True.intro,True.intro⟩,⟨sg12986,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_1All : degreeTree26_1.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg12996,⟨sg12992,⟨sg12990,⟨sg12989,⟨sg12988,True.intro,True.intro⟩,True.intro⟩,⟨sg12991,True.intro,True.intro⟩⟩,⟨sg12994,⟨sg12993,True.intro,True.intro⟩,⟨sg12995,True.intro,True.intro⟩⟩⟩,⟨sg13000,⟨sg12998,⟨sg12997,True.intro,True.intro⟩,⟨sg12999,True.intro,True.intro⟩⟩,⟨sg13002,⟨sg13001,True.intro,True.intro⟩,⟨sg13003,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_2All : degreeTree26_2.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg12987,degreeTree26_0All,degreeTree26_1All⟩

lemma degreeTree26_3All : degreeTree26_3.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13013,⟨sg13009,⟨sg13007,⟨sg13006,⟨sg13005,True.intro,True.intro⟩,True.intro⟩,⟨sg13008,True.intro,True.intro⟩⟩,⟨sg13011,⟨sg13010,True.intro,True.intro⟩,⟨sg13012,True.intro,True.intro⟩⟩⟩,⟨sg13017,⟨sg13015,⟨sg13014,True.intro,True.intro⟩,⟨sg13016,True.intro,True.intro⟩⟩,⟨sg13019,⟨sg13018,True.intro,True.intro⟩,⟨sg13020,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_4All : degreeTree26_4.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13029,⟨sg13025,⟨sg13023,⟨sg13022,True.intro,True.intro⟩,⟨sg13024,True.intro,True.intro⟩⟩,⟨sg13027,⟨sg13026,True.intro,True.intro⟩,⟨sg13028,True.intro,True.intro⟩⟩⟩,⟨sg13033,⟨sg13031,⟨sg13030,True.intro,True.intro⟩,⟨sg13032,True.intro,True.intro⟩⟩,⟨sg13035,⟨sg13034,True.intro,True.intro⟩,⟨sg13036,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_5All : degreeTree26_5.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13021,degreeTree26_3All,degreeTree26_4All⟩

lemma degreeTree26_6All : degreeTree26_6.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13004,degreeTree26_2All,degreeTree26_5All⟩

lemma degreeTree26_7All : degreeTree26_7.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13046,⟨sg13042,⟨sg13040,⟨sg13039,⟨sg13038,True.intro,True.intro⟩,True.intro⟩,⟨sg13041,True.intro,True.intro⟩⟩,⟨sg13044,⟨sg13043,True.intro,True.intro⟩,⟨sg13045,True.intro,True.intro⟩⟩⟩,⟨sg13050,⟨sg13048,⟨sg13047,True.intro,True.intro⟩,⟨sg13049,True.intro,True.intro⟩⟩,⟨sg13052,⟨sg13051,True.intro,True.intro⟩,⟨sg13053,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_8All : degreeTree26_8.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13062,⟨sg13058,⟨sg13056,⟨sg13055,True.intro,True.intro⟩,⟨sg13057,True.intro,True.intro⟩⟩,⟨sg13060,⟨sg13059,True.intro,True.intro⟩,⟨sg13061,True.intro,True.intro⟩⟩⟩,⟨sg13066,⟨sg13064,⟨sg13063,True.intro,True.intro⟩,⟨sg13065,True.intro,True.intro⟩⟩,⟨sg13068,⟨sg13067,True.intro,True.intro⟩,⟨sg13069,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_9All : degreeTree26_9.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13054,degreeTree26_7All,degreeTree26_8All⟩

lemma degreeTree26_10All : degreeTree26_10.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13079,⟨sg13075,⟨sg13073,⟨sg13072,⟨sg13071,True.intro,True.intro⟩,True.intro⟩,⟨sg13074,True.intro,True.intro⟩⟩,⟨sg13077,⟨sg13076,True.intro,True.intro⟩,⟨sg13078,True.intro,True.intro⟩⟩⟩,⟨sg13083,⟨sg13081,⟨sg13080,True.intro,True.intro⟩,⟨sg13082,True.intro,True.intro⟩⟩,⟨sg13085,⟨sg13084,True.intro,True.intro⟩,⟨sg13086,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_11All : degreeTree26_11.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13095,⟨sg13091,⟨sg13089,⟨sg13088,True.intro,True.intro⟩,⟨sg13090,True.intro,True.intro⟩⟩,⟨sg13093,⟨sg13092,True.intro,True.intro⟩,⟨sg13094,True.intro,True.intro⟩⟩⟩,⟨sg13099,⟨sg13097,⟨sg13096,True.intro,True.intro⟩,⟨sg13098,True.intro,True.intro⟩⟩,⟨sg13101,⟨sg13100,True.intro,True.intro⟩,⟨sg13102,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_12All : degreeTree26_12.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13087,degreeTree26_10All,degreeTree26_11All⟩

lemma degreeTree26_13All : degreeTree26_13.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13070,degreeTree26_9All,degreeTree26_12All⟩

lemma degreeTree26_14All : degreeTree26_14.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13037,degreeTree26_6All,degreeTree26_13All⟩

lemma degreeTree26_15All : degreeTree26_15.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13112,⟨sg13108,⟨sg13106,⟨sg13105,⟨sg13104,True.intro,True.intro⟩,True.intro⟩,⟨sg13107,True.intro,True.intro⟩⟩,⟨sg13110,⟨sg13109,True.intro,True.intro⟩,⟨sg13111,True.intro,True.intro⟩⟩⟩,⟨sg13116,⟨sg13114,⟨sg13113,True.intro,True.intro⟩,⟨sg13115,True.intro,True.intro⟩⟩,⟨sg13118,⟨sg13117,True.intro,True.intro⟩,⟨sg13119,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_16All : degreeTree26_16.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13128,⟨sg13124,⟨sg13122,⟨sg13121,True.intro,True.intro⟩,⟨sg13123,True.intro,True.intro⟩⟩,⟨sg13126,⟨sg13125,True.intro,True.intro⟩,⟨sg13127,True.intro,True.intro⟩⟩⟩,⟨sg13132,⟨sg13130,⟨sg13129,True.intro,True.intro⟩,⟨sg13131,True.intro,True.intro⟩⟩,⟨sg13134,⟨sg13133,True.intro,True.intro⟩,⟨sg13135,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_17All : degreeTree26_17.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13120,degreeTree26_15All,degreeTree26_16All⟩

lemma degreeTree26_18All : degreeTree26_18.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13145,⟨sg13141,⟨sg13139,⟨sg13138,⟨sg13137,True.intro,True.intro⟩,True.intro⟩,⟨sg13140,True.intro,True.intro⟩⟩,⟨sg13143,⟨sg13142,True.intro,True.intro⟩,⟨sg13144,True.intro,True.intro⟩⟩⟩,⟨sg13149,⟨sg13147,⟨sg13146,True.intro,True.intro⟩,⟨sg13148,True.intro,True.intro⟩⟩,⟨sg13151,⟨sg13150,True.intro,True.intro⟩,⟨sg13152,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_19All : degreeTree26_19.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13161,⟨sg13157,⟨sg13155,⟨sg13154,True.intro,True.intro⟩,⟨sg13156,True.intro,True.intro⟩⟩,⟨sg13159,⟨sg13158,True.intro,True.intro⟩,⟨sg13160,True.intro,True.intro⟩⟩⟩,⟨sg13165,⟨sg13163,⟨sg13162,True.intro,True.intro⟩,⟨sg13164,True.intro,True.intro⟩⟩,⟨sg13167,⟨sg13166,True.intro,True.intro⟩,⟨sg13168,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_20All : degreeTree26_20.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13153,degreeTree26_18All,degreeTree26_19All⟩

lemma degreeTree26_21All : degreeTree26_21.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13136,degreeTree26_17All,degreeTree26_20All⟩

lemma degreeTree26_22All : degreeTree26_22.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13178,⟨sg13174,⟨sg13172,⟨sg13171,⟨sg13170,True.intro,True.intro⟩,True.intro⟩,⟨sg13173,True.intro,True.intro⟩⟩,⟨sg13176,⟨sg13175,True.intro,True.intro⟩,⟨sg13177,True.intro,True.intro⟩⟩⟩,⟨sg13182,⟨sg13180,⟨sg13179,True.intro,True.intro⟩,⟨sg13181,True.intro,True.intro⟩⟩,⟨sg13184,⟨sg13183,True.intro,True.intro⟩,⟨sg13185,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_23All : degreeTree26_23.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13194,⟨sg13190,⟨sg13188,⟨sg13187,True.intro,True.intro⟩,⟨sg13189,True.intro,True.intro⟩⟩,⟨sg13192,⟨sg13191,True.intro,True.intro⟩,⟨sg13193,True.intro,True.intro⟩⟩⟩,⟨sg13198,⟨sg13196,⟨sg13195,True.intro,True.intro⟩,⟨sg13197,True.intro,True.intro⟩⟩,⟨sg13200,⟨sg13199,True.intro,True.intro⟩,⟨sg13201,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_24All : degreeTree26_24.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13186,degreeTree26_22All,degreeTree26_23All⟩

lemma degreeTree26_25All : degreeTree26_25.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13211,⟨sg13207,⟨sg13205,⟨sg13204,⟨sg13203,True.intro,True.intro⟩,True.intro⟩,⟨sg13206,True.intro,True.intro⟩⟩,⟨sg13209,⟨sg13208,True.intro,True.intro⟩,⟨sg13210,True.intro,True.intro⟩⟩⟩,⟨sg13215,⟨sg13213,⟨sg13212,True.intro,True.intro⟩,⟨sg13214,True.intro,True.intro⟩⟩,⟨sg13217,⟨sg13216,True.intro,True.intro⟩,⟨sg13218,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_26All : degreeTree26_26.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13227,⟨sg13223,⟨sg13221,⟨sg13220,True.intro,True.intro⟩,⟨sg13222,True.intro,True.intro⟩⟩,⟨sg13225,⟨sg13224,True.intro,True.intro⟩,⟨sg13226,True.intro,True.intro⟩⟩⟩,⟨sg13231,⟨sg13229,⟨sg13228,True.intro,True.intro⟩,⟨sg13230,True.intro,True.intro⟩⟩,⟨sg13233,⟨sg13232,True.intro,True.intro⟩,⟨sg13234,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_27All : degreeTree26_27.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13219,degreeTree26_25All,degreeTree26_26All⟩

lemma degreeTree26_28All : degreeTree26_28.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13202,degreeTree26_24All,degreeTree26_27All⟩

lemma degreeTree26_29All : degreeTree26_29.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13169,degreeTree26_21All,degreeTree26_28All⟩

lemma degreeTree26_30All : degreeTree26_30.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13103,degreeTree26_14All,degreeTree26_29All⟩

lemma degreeTree26_31All : degreeTree26_31.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13244,⟨sg13240,⟨sg13238,⟨sg13237,⟨sg13236,True.intro,True.intro⟩,True.intro⟩,⟨sg13239,True.intro,True.intro⟩⟩,⟨sg13242,⟨sg13241,True.intro,True.intro⟩,⟨sg13243,True.intro,True.intro⟩⟩⟩,⟨sg13248,⟨sg13246,⟨sg13245,True.intro,True.intro⟩,⟨sg13247,True.intro,True.intro⟩⟩,⟨sg13250,⟨sg13249,True.intro,True.intro⟩,⟨sg13251,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_32All : degreeTree26_32.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13260,⟨sg13256,⟨sg13254,⟨sg13253,True.intro,True.intro⟩,⟨sg13255,True.intro,True.intro⟩⟩,⟨sg13258,⟨sg13257,True.intro,True.intro⟩,⟨sg13259,True.intro,True.intro⟩⟩⟩,⟨sg13264,⟨sg13262,⟨sg13261,True.intro,True.intro⟩,⟨sg13263,True.intro,True.intro⟩⟩,⟨sg13266,⟨sg13265,True.intro,True.intro⟩,⟨sg13267,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_33All : degreeTree26_33.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13252,degreeTree26_31All,degreeTree26_32All⟩

lemma degreeTree26_34All : degreeTree26_34.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13277,⟨sg13273,⟨sg13271,⟨sg13270,⟨sg13269,True.intro,True.intro⟩,True.intro⟩,⟨sg13272,True.intro,True.intro⟩⟩,⟨sg13275,⟨sg13274,True.intro,True.intro⟩,⟨sg13276,True.intro,True.intro⟩⟩⟩,⟨sg13281,⟨sg13279,⟨sg13278,True.intro,True.intro⟩,⟨sg13280,True.intro,True.intro⟩⟩,⟨sg13283,⟨sg13282,True.intro,True.intro⟩,⟨sg13284,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_35All : degreeTree26_35.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13293,⟨sg13289,⟨sg13287,⟨sg13286,True.intro,True.intro⟩,⟨sg13288,True.intro,True.intro⟩⟩,⟨sg13291,⟨sg13290,True.intro,True.intro⟩,⟨sg13292,True.intro,True.intro⟩⟩⟩,⟨sg13297,⟨sg13295,⟨sg13294,True.intro,True.intro⟩,⟨sg13296,True.intro,True.intro⟩⟩,⟨sg13299,⟨sg13298,True.intro,True.intro⟩,⟨sg13300,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_36All : degreeTree26_36.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13285,degreeTree26_34All,degreeTree26_35All⟩

lemma degreeTree26_37All : degreeTree26_37.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13268,degreeTree26_33All,degreeTree26_36All⟩

lemma degreeTree26_38All : degreeTree26_38.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13310,⟨sg13306,⟨sg13304,⟨sg13303,⟨sg13302,True.intro,True.intro⟩,True.intro⟩,⟨sg13305,True.intro,True.intro⟩⟩,⟨sg13308,⟨sg13307,True.intro,True.intro⟩,⟨sg13309,True.intro,True.intro⟩⟩⟩,⟨sg13314,⟨sg13312,⟨sg13311,True.intro,True.intro⟩,⟨sg13313,True.intro,True.intro⟩⟩,⟨sg13316,⟨sg13315,True.intro,True.intro⟩,⟨sg13317,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_39All : degreeTree26_39.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13326,⟨sg13322,⟨sg13320,⟨sg13319,True.intro,True.intro⟩,⟨sg13321,True.intro,True.intro⟩⟩,⟨sg13324,⟨sg13323,True.intro,True.intro⟩,⟨sg13325,True.intro,True.intro⟩⟩⟩,⟨sg13330,⟨sg13328,⟨sg13327,True.intro,True.intro⟩,⟨sg13329,True.intro,True.intro⟩⟩,⟨sg13332,⟨sg13331,True.intro,True.intro⟩,⟨sg13333,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_40All : degreeTree26_40.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13318,degreeTree26_38All,degreeTree26_39All⟩

lemma degreeTree26_41All : degreeTree26_41.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13343,⟨sg13339,⟨sg13337,⟨sg13336,⟨sg13335,True.intro,True.intro⟩,True.intro⟩,⟨sg13338,True.intro,True.intro⟩⟩,⟨sg13341,⟨sg13340,True.intro,True.intro⟩,⟨sg13342,True.intro,True.intro⟩⟩⟩,⟨sg13347,⟨sg13345,⟨sg13344,True.intro,True.intro⟩,⟨sg13346,True.intro,True.intro⟩⟩,⟨sg13349,⟨sg13348,True.intro,True.intro⟩,⟨sg13350,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_42All : degreeTree26_42.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13359,⟨sg13355,⟨sg13353,⟨sg13352,True.intro,True.intro⟩,⟨sg13354,True.intro,True.intro⟩⟩,⟨sg13357,⟨sg13356,True.intro,True.intro⟩,⟨sg13358,True.intro,True.intro⟩⟩⟩,⟨sg13363,⟨sg13361,⟨sg13360,True.intro,True.intro⟩,⟨sg13362,True.intro,True.intro⟩⟩,⟨sg13365,⟨sg13364,True.intro,True.intro⟩,⟨sg13366,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_43All : degreeTree26_43.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13351,degreeTree26_41All,degreeTree26_42All⟩

lemma degreeTree26_44All : degreeTree26_44.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13334,degreeTree26_40All,degreeTree26_43All⟩

lemma degreeTree26_45All : degreeTree26_45.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13301,degreeTree26_37All,degreeTree26_44All⟩

lemma degreeTree26_46All : degreeTree26_46.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13376,⟨sg13372,⟨sg13370,⟨sg13369,⟨sg13368,True.intro,True.intro⟩,True.intro⟩,⟨sg13371,True.intro,True.intro⟩⟩,⟨sg13374,⟨sg13373,True.intro,True.intro⟩,⟨sg13375,True.intro,True.intro⟩⟩⟩,⟨sg13380,⟨sg13378,⟨sg13377,True.intro,True.intro⟩,⟨sg13379,True.intro,True.intro⟩⟩,⟨sg13382,⟨sg13381,True.intro,True.intro⟩,⟨sg13383,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_47All : degreeTree26_47.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13392,⟨sg13388,⟨sg13386,⟨sg13385,True.intro,True.intro⟩,⟨sg13387,True.intro,True.intro⟩⟩,⟨sg13390,⟨sg13389,True.intro,True.intro⟩,⟨sg13391,True.intro,True.intro⟩⟩⟩,⟨sg13396,⟨sg13394,⟨sg13393,True.intro,True.intro⟩,⟨sg13395,True.intro,True.intro⟩⟩,⟨sg13398,⟨sg13397,True.intro,True.intro⟩,⟨sg13399,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_48All : degreeTree26_48.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13384,degreeTree26_46All,degreeTree26_47All⟩

lemma degreeTree26_49All : degreeTree26_49.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13409,⟨sg13405,⟨sg13403,⟨sg13402,⟨sg13401,True.intro,True.intro⟩,True.intro⟩,⟨sg13404,True.intro,True.intro⟩⟩,⟨sg13407,⟨sg13406,True.intro,True.intro⟩,⟨sg13408,True.intro,True.intro⟩⟩⟩,⟨sg13413,⟨sg13411,⟨sg13410,True.intro,True.intro⟩,⟨sg13412,True.intro,True.intro⟩⟩,⟨sg13415,⟨sg13414,True.intro,True.intro⟩,⟨sg13416,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_50All : degreeTree26_50.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13425,⟨sg13421,⟨sg13419,⟨sg13418,True.intro,True.intro⟩,⟨sg13420,True.intro,True.intro⟩⟩,⟨sg13423,⟨sg13422,True.intro,True.intro⟩,⟨sg13424,True.intro,True.intro⟩⟩⟩,⟨sg13429,⟨sg13427,⟨sg13426,True.intro,True.intro⟩,⟨sg13428,True.intro,True.intro⟩⟩,⟨sg13431,⟨sg13430,True.intro,True.intro⟩,⟨sg13432,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_51All : degreeTree26_51.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13417,degreeTree26_49All,degreeTree26_50All⟩

lemma degreeTree26_52All : degreeTree26_52.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13400,degreeTree26_48All,degreeTree26_51All⟩

lemma degreeTree26_53All : degreeTree26_53.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13442,⟨sg13438,⟨sg13436,⟨sg13435,⟨sg13434,True.intro,True.intro⟩,True.intro⟩,⟨sg13437,True.intro,True.intro⟩⟩,⟨sg13440,⟨sg13439,True.intro,True.intro⟩,⟨sg13441,True.intro,True.intro⟩⟩⟩,⟨sg13446,⟨sg13444,⟨sg13443,True.intro,True.intro⟩,⟨sg13445,True.intro,True.intro⟩⟩,⟨sg13448,⟨sg13447,True.intro,True.intro⟩,⟨sg13449,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_54All : degreeTree26_54.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13458,⟨sg13454,⟨sg13452,⟨sg13451,True.intro,True.intro⟩,⟨sg13453,True.intro,True.intro⟩⟩,⟨sg13456,⟨sg13455,True.intro,True.intro⟩,⟨sg13457,True.intro,True.intro⟩⟩⟩,⟨sg13462,⟨sg13460,⟨sg13459,True.intro,True.intro⟩,⟨sg13461,True.intro,True.intro⟩⟩,⟨sg13464,⟨sg13463,True.intro,True.intro⟩,⟨sg13465,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_55All : degreeTree26_55.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13450,degreeTree26_53All,degreeTree26_54All⟩

lemma degreeTree26_56All : degreeTree26_56.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13475,⟨sg13471,⟨sg13469,⟨sg13468,⟨sg13467,True.intro,True.intro⟩,True.intro⟩,⟨sg13470,True.intro,True.intro⟩⟩,⟨sg13473,⟨sg13472,True.intro,True.intro⟩,⟨sg13474,True.intro,True.intro⟩⟩⟩,⟨sg13479,⟨sg13477,⟨sg13476,True.intro,True.intro⟩,⟨sg13478,True.intro,True.intro⟩⟩,⟨sg13481,⟨sg13480,True.intro,True.intro⟩,⟨sg13482,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_57All : degreeTree26_57.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13491,⟨sg13487,⟨sg13485,⟨sg13484,True.intro,True.intro⟩,⟨sg13486,True.intro,True.intro⟩⟩,⟨sg13489,⟨sg13488,True.intro,True.intro⟩,⟨sg13490,True.intro,True.intro⟩⟩⟩,⟨sg13495,⟨sg13493,⟨sg13492,True.intro,True.intro⟩,⟨sg13494,True.intro,True.intro⟩⟩,⟨sg13497,⟨sg13496,True.intro,True.intro⟩,⟨sg13498,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree26_58All : degreeTree26_58.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13483,degreeTree26_56All,degreeTree26_57All⟩

lemma degreeTree26_59All : degreeTree26_59.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13466,degreeTree26_55All,degreeTree26_58All⟩

lemma degreeTree26_60All : degreeTree26_60.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13433,degreeTree26_52All,degreeTree26_59All⟩

lemma degreeTree26_61All : degreeTree26_61.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13367,degreeTree26_45All,degreeTree26_60All⟩

lemma degreeTree26_62All : degreeTree26_62.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13235,degreeTree26_30All,degreeTree26_61All⟩

lemma degreeTreeAll26 : degreeTree26.All
    (fun rs => SquareOccurs (candidate 4 4 0) (rowDiagram rs)) := by
  have hp : rowDiagram [8,7,2,2,2,2,2,1] = candidate 4 4 0 := rowDiagram_candidate (M := 4) (b := 4) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree26_62All

end UniversalTensorSquare
end
end

end OAI
