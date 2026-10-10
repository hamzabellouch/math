import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes53
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes54
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes55
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes56
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes57

namespace OAI

/-! Degree Tree Proof 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree39_0All : degreeTree39_0.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21685,⟨sg21678,⟨sg21674,⟨sg21672,⟨sg21671,True.intro,True.intro⟩,⟨sg21673,True.intro,True.intro⟩⟩,⟨sg21676,⟨sg21675,True.intro,True.intro⟩,⟨sg21677,True.intro,True.intro⟩⟩⟩,⟨sg21682,⟨sg21680,⟨sg21679,True.intro,True.intro⟩,⟨sg21681,True.intro,True.intro⟩⟩,⟨sg21684,⟨sg21683,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21693,⟨sg21689,⟨sg21687,⟨sg21686,True.intro,True.intro⟩,⟨sg21688,True.intro,True.intro⟩⟩,⟨sg21691,⟨sg21690,True.intro,True.intro⟩,⟨sg21692,True.intro,True.intro⟩⟩⟩,⟨sg21697,⟨sg21695,⟨sg21694,True.intro,True.intro⟩,⟨sg21696,True.intro,True.intro⟩⟩,⟨sg21699,⟨sg21698,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_1All : degreeTree39_1.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21715,⟨sg21708,⟨sg21704,⟨sg21702,⟨sg21701,True.intro,True.intro⟩,⟨sg21703,True.intro,True.intro⟩⟩,⟨sg21706,⟨sg21705,True.intro,True.intro⟩,⟨sg21707,True.intro,True.intro⟩⟩⟩,⟨sg21712,⟨sg21710,⟨sg21709,True.intro,True.intro⟩,⟨sg21711,True.intro,True.intro⟩⟩,⟨sg21714,⟨sg21713,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21722,⟨sg21719,⟨sg21717,⟨sg21716,True.intro,True.intro⟩,⟨sg21718,True.intro,True.intro⟩⟩,⟨sg21721,⟨sg21720,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21726,⟨sg21724,⟨sg21723,True.intro,True.intro⟩,⟨sg21725,True.intro,True.intro⟩⟩,⟨sg21728,⟨sg21727,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_2All : degreeTree39_2.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21700,degreeTree39_0All,degreeTree39_1All⟩

lemma degreeTree39_3All : degreeTree39_3.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21744,⟨sg21737,⟨sg21733,⟨sg21731,⟨sg21730,True.intro,True.intro⟩,⟨sg21732,True.intro,True.intro⟩⟩,⟨sg21735,⟨sg21734,True.intro,True.intro⟩,⟨sg21736,True.intro,True.intro⟩⟩⟩,⟨sg21741,⟨sg21739,⟨sg21738,True.intro,True.intro⟩,⟨sg21740,True.intro,True.intro⟩⟩,⟨sg21743,⟨sg21742,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21751,⟨sg21748,⟨sg21746,⟨sg21745,True.intro,True.intro⟩,⟨sg21747,True.intro,True.intro⟩⟩,⟨sg21750,⟨sg21749,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21755,⟨sg21753,⟨sg21752,True.intro,True.intro⟩,⟨sg21754,True.intro,True.intro⟩⟩,⟨sg21757,⟨sg21756,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_4All : degreeTree39_4.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21773,⟨sg21766,⟨sg21762,⟨sg21760,⟨sg21759,True.intro,True.intro⟩,⟨sg21761,True.intro,True.intro⟩⟩,⟨sg21764,⟨sg21763,True.intro,True.intro⟩,⟨sg21765,True.intro,True.intro⟩⟩⟩,⟨sg21770,⟨sg21768,⟨sg21767,True.intro,True.intro⟩,⟨sg21769,True.intro,True.intro⟩⟩,⟨sg21772,⟨sg21771,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21780,⟨sg21777,⟨sg21775,⟨sg21774,True.intro,True.intro⟩,⟨sg21776,True.intro,True.intro⟩⟩,⟨sg21779,⟨sg21778,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21784,⟨sg21782,⟨sg21781,True.intro,True.intro⟩,⟨sg21783,True.intro,True.intro⟩⟩,⟨sg21786,⟨sg21785,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_5All : degreeTree39_5.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21758,degreeTree39_3All,degreeTree39_4All⟩

lemma degreeTree39_6All : degreeTree39_6.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21729,degreeTree39_2All,degreeTree39_5All⟩

lemma degreeTree39_7All : degreeTree39_7.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21802,⟨sg21795,⟨sg21791,⟨sg21789,⟨sg21788,True.intro,True.intro⟩,⟨sg21790,True.intro,True.intro⟩⟩,⟨sg21793,⟨sg21792,True.intro,True.intro⟩,⟨sg21794,True.intro,True.intro⟩⟩⟩,⟨sg21799,⟨sg21797,⟨sg21796,True.intro,True.intro⟩,⟨sg21798,True.intro,True.intro⟩⟩,⟨sg21801,⟨sg21800,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21809,⟨sg21806,⟨sg21804,⟨sg21803,True.intro,True.intro⟩,⟨sg21805,True.intro,True.intro⟩⟩,⟨sg21808,⟨sg21807,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21813,⟨sg21811,⟨sg21810,True.intro,True.intro⟩,⟨sg21812,True.intro,True.intro⟩⟩,⟨sg21815,⟨sg21814,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_8All : degreeTree39_8.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21831,⟨sg21824,⟨sg21820,⟨sg21818,⟨sg21817,True.intro,True.intro⟩,⟨sg21819,True.intro,True.intro⟩⟩,⟨sg21822,⟨sg21821,True.intro,True.intro⟩,⟨sg21823,True.intro,True.intro⟩⟩⟩,⟨sg21828,⟨sg21826,⟨sg21825,True.intro,True.intro⟩,⟨sg21827,True.intro,True.intro⟩⟩,⟨sg21830,⟨sg21829,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21838,⟨sg21835,⟨sg21833,⟨sg21832,True.intro,True.intro⟩,⟨sg21834,True.intro,True.intro⟩⟩,⟨sg21837,⟨sg21836,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21842,⟨sg21840,⟨sg21839,True.intro,True.intro⟩,⟨sg21841,True.intro,True.intro⟩⟩,⟨sg21844,⟨sg21843,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_9All : degreeTree39_9.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21816,degreeTree39_7All,degreeTree39_8All⟩

lemma degreeTree39_10All : degreeTree39_10.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21860,⟨sg21853,⟨sg21849,⟨sg21847,⟨sg21846,True.intro,True.intro⟩,⟨sg21848,True.intro,True.intro⟩⟩,⟨sg21851,⟨sg21850,True.intro,True.intro⟩,⟨sg21852,True.intro,True.intro⟩⟩⟩,⟨sg21857,⟨sg21855,⟨sg21854,True.intro,True.intro⟩,⟨sg21856,True.intro,True.intro⟩⟩,⟨sg21859,⟨sg21858,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21867,⟨sg21864,⟨sg21862,⟨sg21861,True.intro,True.intro⟩,⟨sg21863,True.intro,True.intro⟩⟩,⟨sg21866,⟨sg21865,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21871,⟨sg21869,⟨sg21868,True.intro,True.intro⟩,⟨sg21870,True.intro,True.intro⟩⟩,⟨sg21873,⟨sg21872,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_11All : degreeTree39_11.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21889,⟨sg21882,⟨sg21878,⟨sg21876,⟨sg21875,True.intro,True.intro⟩,⟨sg21877,True.intro,True.intro⟩⟩,⟨sg21880,⟨sg21879,True.intro,True.intro⟩,⟨sg21881,True.intro,True.intro⟩⟩⟩,⟨sg21886,⟨sg21884,⟨sg21883,True.intro,True.intro⟩,⟨sg21885,True.intro,True.intro⟩⟩,⟨sg21888,⟨sg21887,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21896,⟨sg21893,⟨sg21891,⟨sg21890,True.intro,True.intro⟩,⟨sg21892,True.intro,True.intro⟩⟩,⟨sg21895,⟨sg21894,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21900,⟨sg21898,⟨sg21897,True.intro,True.intro⟩,⟨sg21899,True.intro,True.intro⟩⟩,⟨sg21902,⟨sg21901,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_12All : degreeTree39_12.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21874,degreeTree39_10All,degreeTree39_11All⟩

lemma degreeTree39_13All : degreeTree39_13.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21845,degreeTree39_9All,degreeTree39_12All⟩

lemma degreeTree39_14All : degreeTree39_14.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21787,degreeTree39_6All,degreeTree39_13All⟩

lemma degreeTree39_15All : degreeTree39_15.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21918,⟨sg21911,⟨sg21907,⟨sg21905,⟨sg21904,True.intro,True.intro⟩,⟨sg21906,True.intro,True.intro⟩⟩,⟨sg21909,⟨sg21908,True.intro,True.intro⟩,⟨sg21910,True.intro,True.intro⟩⟩⟩,⟨sg21915,⟨sg21913,⟨sg21912,True.intro,True.intro⟩,⟨sg21914,True.intro,True.intro⟩⟩,⟨sg21917,⟨sg21916,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21925,⟨sg21922,⟨sg21920,⟨sg21919,True.intro,True.intro⟩,⟨sg21921,True.intro,True.intro⟩⟩,⟨sg21924,⟨sg21923,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21929,⟨sg21927,⟨sg21926,True.intro,True.intro⟩,⟨sg21928,True.intro,True.intro⟩⟩,⟨sg21931,⟨sg21930,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_16All : degreeTree39_16.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21947,⟨sg21940,⟨sg21936,⟨sg21934,⟨sg21933,True.intro,True.intro⟩,⟨sg21935,True.intro,True.intro⟩⟩,⟨sg21938,⟨sg21937,True.intro,True.intro⟩,⟨sg21939,True.intro,True.intro⟩⟩⟩,⟨sg21944,⟨sg21942,⟨sg21941,True.intro,True.intro⟩,⟨sg21943,True.intro,True.intro⟩⟩,⟨sg21946,⟨sg21945,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21954,⟨sg21951,⟨sg21949,⟨sg21948,True.intro,True.intro⟩,⟨sg21950,True.intro,True.intro⟩⟩,⟨sg21953,⟨sg21952,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21958,⟨sg21956,⟨sg21955,True.intro,True.intro⟩,⟨sg21957,True.intro,True.intro⟩⟩,⟨sg21960,⟨sg21959,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_17All : degreeTree39_17.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21932,degreeTree39_15All,degreeTree39_16All⟩

lemma degreeTree39_18All : degreeTree39_18.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21976,⟨sg21969,⟨sg21965,⟨sg21963,⟨sg21962,True.intro,True.intro⟩,⟨sg21964,True.intro,True.intro⟩⟩,⟨sg21967,⟨sg21966,True.intro,True.intro⟩,⟨sg21968,True.intro,True.intro⟩⟩⟩,⟨sg21973,⟨sg21971,⟨sg21970,True.intro,True.intro⟩,⟨sg21972,True.intro,True.intro⟩⟩,⟨sg21975,⟨sg21974,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg21983,⟨sg21980,⟨sg21978,⟨sg21977,True.intro,True.intro⟩,⟨sg21979,True.intro,True.intro⟩⟩,⟨sg21982,⟨sg21981,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg21987,⟨sg21985,⟨sg21984,True.intro,True.intro⟩,⟨sg21986,True.intro,True.intro⟩⟩,⟨sg21989,⟨sg21988,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_19All : degreeTree39_19.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22005,⟨sg21998,⟨sg21994,⟨sg21992,⟨sg21991,True.intro,True.intro⟩,⟨sg21993,True.intro,True.intro⟩⟩,⟨sg21996,⟨sg21995,True.intro,True.intro⟩,⟨sg21997,True.intro,True.intro⟩⟩⟩,⟨sg22002,⟨sg22000,⟨sg21999,True.intro,True.intro⟩,⟨sg22001,True.intro,True.intro⟩⟩,⟨sg22004,⟨sg22003,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22012,⟨sg22009,⟨sg22007,⟨sg22006,True.intro,True.intro⟩,⟨sg22008,True.intro,True.intro⟩⟩,⟨sg22011,⟨sg22010,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22016,⟨sg22014,⟨sg22013,True.intro,True.intro⟩,⟨sg22015,True.intro,True.intro⟩⟩,⟨sg22018,⟨sg22017,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_20All : degreeTree39_20.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21990,degreeTree39_18All,degreeTree39_19All⟩

lemma degreeTree39_21All : degreeTree39_21.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21961,degreeTree39_17All,degreeTree39_20All⟩

lemma degreeTree39_22All : degreeTree39_22.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22034,⟨sg22027,⟨sg22023,⟨sg22021,⟨sg22020,True.intro,True.intro⟩,⟨sg22022,True.intro,True.intro⟩⟩,⟨sg22025,⟨sg22024,True.intro,True.intro⟩,⟨sg22026,True.intro,True.intro⟩⟩⟩,⟨sg22031,⟨sg22029,⟨sg22028,True.intro,True.intro⟩,⟨sg22030,True.intro,True.intro⟩⟩,⟨sg22033,⟨sg22032,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22041,⟨sg22038,⟨sg22036,⟨sg22035,True.intro,True.intro⟩,⟨sg22037,True.intro,True.intro⟩⟩,⟨sg22040,⟨sg22039,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22045,⟨sg22043,⟨sg22042,True.intro,True.intro⟩,⟨sg22044,True.intro,True.intro⟩⟩,⟨sg22047,⟨sg22046,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_23All : degreeTree39_23.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22063,⟨sg22056,⟨sg22052,⟨sg22050,⟨sg22049,True.intro,True.intro⟩,⟨sg22051,True.intro,True.intro⟩⟩,⟨sg22054,⟨sg22053,True.intro,True.intro⟩,⟨sg22055,True.intro,True.intro⟩⟩⟩,⟨sg22060,⟨sg22058,⟨sg22057,True.intro,True.intro⟩,⟨sg22059,True.intro,True.intro⟩⟩,⟨sg22062,⟨sg22061,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22070,⟨sg22067,⟨sg22065,⟨sg22064,True.intro,True.intro⟩,⟨sg22066,True.intro,True.intro⟩⟩,⟨sg22069,⟨sg22068,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22074,⟨sg22072,⟨sg22071,True.intro,True.intro⟩,⟨sg22073,True.intro,True.intro⟩⟩,⟨sg22076,⟨sg22075,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_24All : degreeTree39_24.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22048,degreeTree39_22All,degreeTree39_23All⟩

lemma degreeTree39_25All : degreeTree39_25.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22092,⟨sg22085,⟨sg22081,⟨sg22079,⟨sg22078,True.intro,True.intro⟩,⟨sg22080,True.intro,True.intro⟩⟩,⟨sg22083,⟨sg22082,True.intro,True.intro⟩,⟨sg22084,True.intro,True.intro⟩⟩⟩,⟨sg22089,⟨sg22087,⟨sg22086,True.intro,True.intro⟩,⟨sg22088,True.intro,True.intro⟩⟩,⟨sg22091,⟨sg22090,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22099,⟨sg22096,⟨sg22094,⟨sg22093,True.intro,True.intro⟩,⟨sg22095,True.intro,True.intro⟩⟩,⟨sg22098,⟨sg22097,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22103,⟨sg22101,⟨sg22100,True.intro,True.intro⟩,⟨sg22102,True.intro,True.intro⟩⟩,⟨sg22105,⟨sg22104,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_26All : degreeTree39_26.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22121,⟨sg22114,⟨sg22110,⟨sg22108,⟨sg22107,True.intro,True.intro⟩,⟨sg22109,True.intro,True.intro⟩⟩,⟨sg22112,⟨sg22111,True.intro,True.intro⟩,⟨sg22113,True.intro,True.intro⟩⟩⟩,⟨sg22118,⟨sg22116,⟨sg22115,True.intro,True.intro⟩,⟨sg22117,True.intro,True.intro⟩⟩,⟨sg22120,⟨sg22119,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22128,⟨sg22125,⟨sg22123,⟨sg22122,True.intro,True.intro⟩,⟨sg22124,True.intro,True.intro⟩⟩,⟨sg22127,⟨sg22126,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22132,⟨sg22130,⟨sg22129,True.intro,True.intro⟩,⟨sg22131,True.intro,True.intro⟩⟩,⟨sg22134,⟨sg22133,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_27All : degreeTree39_27.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22106,degreeTree39_25All,degreeTree39_26All⟩

lemma degreeTree39_28All : degreeTree39_28.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22077,degreeTree39_24All,degreeTree39_27All⟩

lemma degreeTree39_29All : degreeTree39_29.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22019,degreeTree39_21All,degreeTree39_28All⟩

lemma degreeTree39_30All : degreeTree39_30.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg21903,degreeTree39_14All,degreeTree39_29All⟩

lemma degreeTree39_31All : degreeTree39_31.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22150,⟨sg22143,⟨sg22139,⟨sg22137,⟨sg22136,True.intro,True.intro⟩,⟨sg22138,True.intro,True.intro⟩⟩,⟨sg22141,⟨sg22140,True.intro,True.intro⟩,⟨sg22142,True.intro,True.intro⟩⟩⟩,⟨sg22147,⟨sg22145,⟨sg22144,True.intro,True.intro⟩,⟨sg22146,True.intro,True.intro⟩⟩,⟨sg22149,⟨sg22148,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22158,⟨sg22154,⟨sg22152,⟨sg22151,True.intro,True.intro⟩,⟨sg22153,True.intro,True.intro⟩⟩,⟨sg22156,⟨sg22155,True.intro,True.intro⟩,⟨sg22157,True.intro,True.intro⟩⟩⟩,⟨sg22162,⟨sg22160,⟨sg22159,True.intro,True.intro⟩,⟨sg22161,True.intro,True.intro⟩⟩,⟨sg22164,⟨sg22163,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_32All : degreeTree39_32.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22180,⟨sg22173,⟨sg22169,⟨sg22167,⟨sg22166,True.intro,True.intro⟩,⟨sg22168,True.intro,True.intro⟩⟩,⟨sg22171,⟨sg22170,True.intro,True.intro⟩,⟨sg22172,True.intro,True.intro⟩⟩⟩,⟨sg22177,⟨sg22175,⟨sg22174,True.intro,True.intro⟩,⟨sg22176,True.intro,True.intro⟩⟩,⟨sg22179,⟨sg22178,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22187,⟨sg22184,⟨sg22182,⟨sg22181,True.intro,True.intro⟩,⟨sg22183,True.intro,True.intro⟩⟩,⟨sg22186,⟨sg22185,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22191,⟨sg22189,⟨sg22188,True.intro,True.intro⟩,⟨sg22190,True.intro,True.intro⟩⟩,⟨sg22193,⟨sg22192,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_33All : degreeTree39_33.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22165,degreeTree39_31All,degreeTree39_32All⟩

lemma degreeTree39_34All : degreeTree39_34.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22209,⟨sg22202,⟨sg22198,⟨sg22196,⟨sg22195,True.intro,True.intro⟩,⟨sg22197,True.intro,True.intro⟩⟩,⟨sg22200,⟨sg22199,True.intro,True.intro⟩,⟨sg22201,True.intro,True.intro⟩⟩⟩,⟨sg22206,⟨sg22204,⟨sg22203,True.intro,True.intro⟩,⟨sg22205,True.intro,True.intro⟩⟩,⟨sg22208,⟨sg22207,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22216,⟨sg22213,⟨sg22211,⟨sg22210,True.intro,True.intro⟩,⟨sg22212,True.intro,True.intro⟩⟩,⟨sg22215,⟨sg22214,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22220,⟨sg22218,⟨sg22217,True.intro,True.intro⟩,⟨sg22219,True.intro,True.intro⟩⟩,⟨sg22222,⟨sg22221,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_35All : degreeTree39_35.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22238,⟨sg22231,⟨sg22227,⟨sg22225,⟨sg22224,True.intro,True.intro⟩,⟨sg22226,True.intro,True.intro⟩⟩,⟨sg22229,⟨sg22228,True.intro,True.intro⟩,⟨sg22230,True.intro,True.intro⟩⟩⟩,⟨sg22235,⟨sg22233,⟨sg22232,True.intro,True.intro⟩,⟨sg22234,True.intro,True.intro⟩⟩,⟨sg22237,⟨sg22236,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22245,⟨sg22242,⟨sg22240,⟨sg22239,True.intro,True.intro⟩,⟨sg22241,True.intro,True.intro⟩⟩,⟨sg22244,⟨sg22243,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22249,⟨sg22247,⟨sg22246,True.intro,True.intro⟩,⟨sg22248,True.intro,True.intro⟩⟩,⟨sg22251,⟨sg22250,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_36All : degreeTree39_36.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22223,degreeTree39_34All,degreeTree39_35All⟩

lemma degreeTree39_37All : degreeTree39_37.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22194,degreeTree39_33All,degreeTree39_36All⟩

lemma degreeTree39_38All : degreeTree39_38.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22267,⟨sg22260,⟨sg22256,⟨sg22254,⟨sg22253,True.intro,True.intro⟩,⟨sg22255,True.intro,True.intro⟩⟩,⟨sg22258,⟨sg22257,True.intro,True.intro⟩,⟨sg22259,True.intro,True.intro⟩⟩⟩,⟨sg22264,⟨sg22262,⟨sg22261,True.intro,True.intro⟩,⟨sg22263,True.intro,True.intro⟩⟩,⟨sg22266,⟨sg22265,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22274,⟨sg22271,⟨sg22269,⟨sg22268,True.intro,True.intro⟩,⟨sg22270,True.intro,True.intro⟩⟩,⟨sg22273,⟨sg22272,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22278,⟨sg22276,⟨sg22275,True.intro,True.intro⟩,⟨sg22277,True.intro,True.intro⟩⟩,⟨sg22280,⟨sg22279,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_39All : degreeTree39_39.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22296,⟨sg22289,⟨sg22285,⟨sg22283,⟨sg22282,True.intro,True.intro⟩,⟨sg22284,True.intro,True.intro⟩⟩,⟨sg22287,⟨sg22286,True.intro,True.intro⟩,⟨sg22288,True.intro,True.intro⟩⟩⟩,⟨sg22293,⟨sg22291,⟨sg22290,True.intro,True.intro⟩,⟨sg22292,True.intro,True.intro⟩⟩,⟨sg22295,⟨sg22294,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22303,⟨sg22300,⟨sg22298,⟨sg22297,True.intro,True.intro⟩,⟨sg22299,True.intro,True.intro⟩⟩,⟨sg22302,⟨sg22301,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22307,⟨sg22305,⟨sg22304,True.intro,True.intro⟩,⟨sg22306,True.intro,True.intro⟩⟩,⟨sg22309,⟨sg22308,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_40All : degreeTree39_40.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22281,degreeTree39_38All,degreeTree39_39All⟩

lemma degreeTree39_41All : degreeTree39_41.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22325,⟨sg22318,⟨sg22314,⟨sg22312,⟨sg22311,True.intro,True.intro⟩,⟨sg22313,True.intro,True.intro⟩⟩,⟨sg22316,⟨sg22315,True.intro,True.intro⟩,⟨sg22317,True.intro,True.intro⟩⟩⟩,⟨sg22322,⟨sg22320,⟨sg22319,True.intro,True.intro⟩,⟨sg22321,True.intro,True.intro⟩⟩,⟨sg22324,⟨sg22323,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22332,⟨sg22329,⟨sg22327,⟨sg22326,True.intro,True.intro⟩,⟨sg22328,True.intro,True.intro⟩⟩,⟨sg22331,⟨sg22330,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22336,⟨sg22334,⟨sg22333,True.intro,True.intro⟩,⟨sg22335,True.intro,True.intro⟩⟩,⟨sg22338,⟨sg22337,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_42All : degreeTree39_42.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22354,⟨sg22347,⟨sg22343,⟨sg22341,⟨sg22340,True.intro,True.intro⟩,⟨sg22342,True.intro,True.intro⟩⟩,⟨sg22345,⟨sg22344,True.intro,True.intro⟩,⟨sg22346,True.intro,True.intro⟩⟩⟩,⟨sg22351,⟨sg22349,⟨sg22348,True.intro,True.intro⟩,⟨sg22350,True.intro,True.intro⟩⟩,⟨sg22353,⟨sg22352,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22361,⟨sg22358,⟨sg22356,⟨sg22355,True.intro,True.intro⟩,⟨sg22357,True.intro,True.intro⟩⟩,⟨sg22360,⟨sg22359,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22365,⟨sg22363,⟨sg22362,True.intro,True.intro⟩,⟨sg22364,True.intro,True.intro⟩⟩,⟨sg22367,⟨sg22366,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_43All : degreeTree39_43.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22339,degreeTree39_41All,degreeTree39_42All⟩

lemma degreeTree39_44All : degreeTree39_44.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22310,degreeTree39_40All,degreeTree39_43All⟩

lemma degreeTree39_45All : degreeTree39_45.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22252,degreeTree39_37All,degreeTree39_44All⟩

lemma degreeTree39_46All : degreeTree39_46.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22383,⟨sg22376,⟨sg22372,⟨sg22370,⟨sg22369,True.intro,True.intro⟩,⟨sg22371,True.intro,True.intro⟩⟩,⟨sg22374,⟨sg22373,True.intro,True.intro⟩,⟨sg22375,True.intro,True.intro⟩⟩⟩,⟨sg22380,⟨sg22378,⟨sg22377,True.intro,True.intro⟩,⟨sg22379,True.intro,True.intro⟩⟩,⟨sg22382,⟨sg22381,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22390,⟨sg22387,⟨sg22385,⟨sg22384,True.intro,True.intro⟩,⟨sg22386,True.intro,True.intro⟩⟩,⟨sg22389,⟨sg22388,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22394,⟨sg22392,⟨sg22391,True.intro,True.intro⟩,⟨sg22393,True.intro,True.intro⟩⟩,⟨sg22396,⟨sg22395,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_47All : degreeTree39_47.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22412,⟨sg22405,⟨sg22401,⟨sg22399,⟨sg22398,True.intro,True.intro⟩,⟨sg22400,True.intro,True.intro⟩⟩,⟨sg22403,⟨sg22402,True.intro,True.intro⟩,⟨sg22404,True.intro,True.intro⟩⟩⟩,⟨sg22409,⟨sg22407,⟨sg22406,True.intro,True.intro⟩,⟨sg22408,True.intro,True.intro⟩⟩,⟨sg22411,⟨sg22410,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22419,⟨sg22416,⟨sg22414,⟨sg22413,True.intro,True.intro⟩,⟨sg22415,True.intro,True.intro⟩⟩,⟨sg22418,⟨sg22417,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22423,⟨sg22421,⟨sg22420,True.intro,True.intro⟩,⟨sg22422,True.intro,True.intro⟩⟩,⟨sg22425,⟨sg22424,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_48All : degreeTree39_48.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22397,degreeTree39_46All,degreeTree39_47All⟩

lemma degreeTree39_49All : degreeTree39_49.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22441,⟨sg22434,⟨sg22430,⟨sg22428,⟨sg22427,True.intro,True.intro⟩,⟨sg22429,True.intro,True.intro⟩⟩,⟨sg22432,⟨sg22431,True.intro,True.intro⟩,⟨sg22433,True.intro,True.intro⟩⟩⟩,⟨sg22438,⟨sg22436,⟨sg22435,True.intro,True.intro⟩,⟨sg22437,True.intro,True.intro⟩⟩,⟨sg22440,⟨sg22439,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22448,⟨sg22445,⟨sg22443,⟨sg22442,True.intro,True.intro⟩,⟨sg22444,True.intro,True.intro⟩⟩,⟨sg22447,⟨sg22446,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22452,⟨sg22450,⟨sg22449,True.intro,True.intro⟩,⟨sg22451,True.intro,True.intro⟩⟩,⟨sg22454,⟨sg22453,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_50All : degreeTree39_50.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22470,⟨sg22463,⟨sg22459,⟨sg22457,⟨sg22456,True.intro,True.intro⟩,⟨sg22458,True.intro,True.intro⟩⟩,⟨sg22461,⟨sg22460,True.intro,True.intro⟩,⟨sg22462,True.intro,True.intro⟩⟩⟩,⟨sg22467,⟨sg22465,⟨sg22464,True.intro,True.intro⟩,⟨sg22466,True.intro,True.intro⟩⟩,⟨sg22469,⟨sg22468,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22477,⟨sg22474,⟨sg22472,⟨sg22471,True.intro,True.intro⟩,⟨sg22473,True.intro,True.intro⟩⟩,⟨sg22476,⟨sg22475,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22481,⟨sg22479,⟨sg22478,True.intro,True.intro⟩,⟨sg22480,True.intro,True.intro⟩⟩,⟨sg22483,⟨sg22482,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_51All : degreeTree39_51.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22455,degreeTree39_49All,degreeTree39_50All⟩

lemma degreeTree39_52All : degreeTree39_52.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22426,degreeTree39_48All,degreeTree39_51All⟩

lemma degreeTree39_53All : degreeTree39_53.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22499,⟨sg22492,⟨sg22488,⟨sg22486,⟨sg22485,True.intro,True.intro⟩,⟨sg22487,True.intro,True.intro⟩⟩,⟨sg22490,⟨sg22489,True.intro,True.intro⟩,⟨sg22491,True.intro,True.intro⟩⟩⟩,⟨sg22496,⟨sg22494,⟨sg22493,True.intro,True.intro⟩,⟨sg22495,True.intro,True.intro⟩⟩,⟨sg22498,⟨sg22497,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22506,⟨sg22503,⟨sg22501,⟨sg22500,True.intro,True.intro⟩,⟨sg22502,True.intro,True.intro⟩⟩,⟨sg22505,⟨sg22504,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22510,⟨sg22508,⟨sg22507,True.intro,True.intro⟩,⟨sg22509,True.intro,True.intro⟩⟩,⟨sg22512,⟨sg22511,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_54All : degreeTree39_54.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22528,⟨sg22521,⟨sg22517,⟨sg22515,⟨sg22514,True.intro,True.intro⟩,⟨sg22516,True.intro,True.intro⟩⟩,⟨sg22519,⟨sg22518,True.intro,True.intro⟩,⟨sg22520,True.intro,True.intro⟩⟩⟩,⟨sg22525,⟨sg22523,⟨sg22522,True.intro,True.intro⟩,⟨sg22524,True.intro,True.intro⟩⟩,⟨sg22527,⟨sg22526,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22535,⟨sg22532,⟨sg22530,⟨sg22529,True.intro,True.intro⟩,⟨sg22531,True.intro,True.intro⟩⟩,⟨sg22534,⟨sg22533,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22539,⟨sg22537,⟨sg22536,True.intro,True.intro⟩,⟨sg22538,True.intro,True.intro⟩⟩,⟨sg22541,⟨sg22540,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_55All : degreeTree39_55.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22513,degreeTree39_53All,degreeTree39_54All⟩

lemma degreeTree39_56All : degreeTree39_56.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22557,⟨sg22550,⟨sg22546,⟨sg22544,⟨sg22543,True.intro,True.intro⟩,⟨sg22545,True.intro,True.intro⟩⟩,⟨sg22548,⟨sg22547,True.intro,True.intro⟩,⟨sg22549,True.intro,True.intro⟩⟩⟩,⟨sg22554,⟨sg22552,⟨sg22551,True.intro,True.intro⟩,⟨sg22553,True.intro,True.intro⟩⟩,⟨sg22556,⟨sg22555,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22564,⟨sg22561,⟨sg22559,⟨sg22558,True.intro,True.intro⟩,⟨sg22560,True.intro,True.intro⟩⟩,⟨sg22563,⟨sg22562,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22568,⟨sg22566,⟨sg22565,True.intro,True.intro⟩,⟨sg22567,True.intro,True.intro⟩⟩,⟨sg22570,⟨sg22569,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_57All : degreeTree39_57.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22586,⟨sg22579,⟨sg22575,⟨sg22573,⟨sg22572,True.intro,True.intro⟩,⟨sg22574,True.intro,True.intro⟩⟩,⟨sg22577,⟨sg22576,True.intro,True.intro⟩,⟨sg22578,True.intro,True.intro⟩⟩⟩,⟨sg22583,⟨sg22581,⟨sg22580,True.intro,True.intro⟩,⟨sg22582,True.intro,True.intro⟩⟩,⟨sg22585,⟨sg22584,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22593,⟨sg22590,⟨sg22588,⟨sg22587,True.intro,True.intro⟩,⟨sg22589,True.intro,True.intro⟩⟩,⟨sg22592,⟨sg22591,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22597,⟨sg22595,⟨sg22594,True.intro,True.intro⟩,⟨sg22596,True.intro,True.intro⟩⟩,⟨sg22599,⟨sg22598,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_58All : degreeTree39_58.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22571,degreeTree39_56All,degreeTree39_57All⟩

lemma degreeTree39_59All : degreeTree39_59.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22542,degreeTree39_55All,degreeTree39_58All⟩

lemma degreeTree39_60All : degreeTree39_60.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22484,degreeTree39_52All,degreeTree39_59All⟩

lemma degreeTree39_61All : degreeTree39_61.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22368,degreeTree39_45All,degreeTree39_60All⟩

lemma degreeTree39_62All : degreeTree39_62.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22135,degreeTree39_30All,degreeTree39_61All⟩

lemma degreeTree39_63All : degreeTree39_63.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22615,⟨sg22608,⟨sg22604,⟨sg22602,⟨sg22601,True.intro,True.intro⟩,⟨sg22603,True.intro,True.intro⟩⟩,⟨sg22606,⟨sg22605,True.intro,True.intro⟩,⟨sg22607,True.intro,True.intro⟩⟩⟩,⟨sg22612,⟨sg22610,⟨sg22609,True.intro,True.intro⟩,⟨sg22611,True.intro,True.intro⟩⟩,⟨sg22614,⟨sg22613,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22623,⟨sg22619,⟨sg22617,⟨sg22616,True.intro,True.intro⟩,⟨sg22618,True.intro,True.intro⟩⟩,⟨sg22621,⟨sg22620,True.intro,True.intro⟩,⟨sg22622,True.intro,True.intro⟩⟩⟩,⟨sg22627,⟨sg22625,⟨sg22624,True.intro,True.intro⟩,⟨sg22626,True.intro,True.intro⟩⟩,⟨sg22629,⟨sg22628,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_64All : degreeTree39_64.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22645,⟨sg22638,⟨sg22634,⟨sg22632,⟨sg22631,True.intro,True.intro⟩,⟨sg22633,True.intro,True.intro⟩⟩,⟨sg22636,⟨sg22635,True.intro,True.intro⟩,⟨sg22637,True.intro,True.intro⟩⟩⟩,⟨sg22642,⟨sg22640,⟨sg22639,True.intro,True.intro⟩,⟨sg22641,True.intro,True.intro⟩⟩,⟨sg22644,⟨sg22643,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22652,⟨sg22649,⟨sg22647,⟨sg22646,True.intro,True.intro⟩,⟨sg22648,True.intro,True.intro⟩⟩,⟨sg22651,⟨sg22650,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22656,⟨sg22654,⟨sg22653,True.intro,True.intro⟩,⟨sg22655,True.intro,True.intro⟩⟩,⟨sg22658,⟨sg22657,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_65All : degreeTree39_65.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22630,degreeTree39_63All,degreeTree39_64All⟩

lemma degreeTree39_66All : degreeTree39_66.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22674,⟨sg22667,⟨sg22663,⟨sg22661,⟨sg22660,True.intro,True.intro⟩,⟨sg22662,True.intro,True.intro⟩⟩,⟨sg22665,⟨sg22664,True.intro,True.intro⟩,⟨sg22666,True.intro,True.intro⟩⟩⟩,⟨sg22671,⟨sg22669,⟨sg22668,True.intro,True.intro⟩,⟨sg22670,True.intro,True.intro⟩⟩,⟨sg22673,⟨sg22672,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22681,⟨sg22678,⟨sg22676,⟨sg22675,True.intro,True.intro⟩,⟨sg22677,True.intro,True.intro⟩⟩,⟨sg22680,⟨sg22679,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22685,⟨sg22683,⟨sg22682,True.intro,True.intro⟩,⟨sg22684,True.intro,True.intro⟩⟩,⟨sg22687,⟨sg22686,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_67All : degreeTree39_67.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22703,⟨sg22696,⟨sg22692,⟨sg22690,⟨sg22689,True.intro,True.intro⟩,⟨sg22691,True.intro,True.intro⟩⟩,⟨sg22694,⟨sg22693,True.intro,True.intro⟩,⟨sg22695,True.intro,True.intro⟩⟩⟩,⟨sg22700,⟨sg22698,⟨sg22697,True.intro,True.intro⟩,⟨sg22699,True.intro,True.intro⟩⟩,⟨sg22702,⟨sg22701,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22710,⟨sg22707,⟨sg22705,⟨sg22704,True.intro,True.intro⟩,⟨sg22706,True.intro,True.intro⟩⟩,⟨sg22709,⟨sg22708,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22714,⟨sg22712,⟨sg22711,True.intro,True.intro⟩,⟨sg22713,True.intro,True.intro⟩⟩,⟨sg22716,⟨sg22715,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_68All : degreeTree39_68.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22688,degreeTree39_66All,degreeTree39_67All⟩

lemma degreeTree39_69All : degreeTree39_69.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22659,degreeTree39_65All,degreeTree39_68All⟩

lemma degreeTree39_70All : degreeTree39_70.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22732,⟨sg22725,⟨sg22721,⟨sg22719,⟨sg22718,True.intro,True.intro⟩,⟨sg22720,True.intro,True.intro⟩⟩,⟨sg22723,⟨sg22722,True.intro,True.intro⟩,⟨sg22724,True.intro,True.intro⟩⟩⟩,⟨sg22729,⟨sg22727,⟨sg22726,True.intro,True.intro⟩,⟨sg22728,True.intro,True.intro⟩⟩,⟨sg22731,⟨sg22730,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22739,⟨sg22736,⟨sg22734,⟨sg22733,True.intro,True.intro⟩,⟨sg22735,True.intro,True.intro⟩⟩,⟨sg22738,⟨sg22737,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22743,⟨sg22741,⟨sg22740,True.intro,True.intro⟩,⟨sg22742,True.intro,True.intro⟩⟩,⟨sg22745,⟨sg22744,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_71All : degreeTree39_71.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22761,⟨sg22754,⟨sg22750,⟨sg22748,⟨sg22747,True.intro,True.intro⟩,⟨sg22749,True.intro,True.intro⟩⟩,⟨sg22752,⟨sg22751,True.intro,True.intro⟩,⟨sg22753,True.intro,True.intro⟩⟩⟩,⟨sg22758,⟨sg22756,⟨sg22755,True.intro,True.intro⟩,⟨sg22757,True.intro,True.intro⟩⟩,⟨sg22760,⟨sg22759,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22768,⟨sg22765,⟨sg22763,⟨sg22762,True.intro,True.intro⟩,⟨sg22764,True.intro,True.intro⟩⟩,⟨sg22767,⟨sg22766,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22772,⟨sg22770,⟨sg22769,True.intro,True.intro⟩,⟨sg22771,True.intro,True.intro⟩⟩,⟨sg22774,⟨sg22773,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_72All : degreeTree39_72.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22746,degreeTree39_70All,degreeTree39_71All⟩

lemma degreeTree39_73All : degreeTree39_73.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22790,⟨sg22783,⟨sg22779,⟨sg22777,⟨sg22776,True.intro,True.intro⟩,⟨sg22778,True.intro,True.intro⟩⟩,⟨sg22781,⟨sg22780,True.intro,True.intro⟩,⟨sg22782,True.intro,True.intro⟩⟩⟩,⟨sg22787,⟨sg22785,⟨sg22784,True.intro,True.intro⟩,⟨sg22786,True.intro,True.intro⟩⟩,⟨sg22789,⟨sg22788,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22797,⟨sg22794,⟨sg22792,⟨sg22791,True.intro,True.intro⟩,⟨sg22793,True.intro,True.intro⟩⟩,⟨sg22796,⟨sg22795,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22801,⟨sg22799,⟨sg22798,True.intro,True.intro⟩,⟨sg22800,True.intro,True.intro⟩⟩,⟨sg22803,⟨sg22802,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_74All : degreeTree39_74.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22819,⟨sg22812,⟨sg22808,⟨sg22806,⟨sg22805,True.intro,True.intro⟩,⟨sg22807,True.intro,True.intro⟩⟩,⟨sg22810,⟨sg22809,True.intro,True.intro⟩,⟨sg22811,True.intro,True.intro⟩⟩⟩,⟨sg22816,⟨sg22814,⟨sg22813,True.intro,True.intro⟩,⟨sg22815,True.intro,True.intro⟩⟩,⟨sg22818,⟨sg22817,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22826,⟨sg22823,⟨sg22821,⟨sg22820,True.intro,True.intro⟩,⟨sg22822,True.intro,True.intro⟩⟩,⟨sg22825,⟨sg22824,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22830,⟨sg22828,⟨sg22827,True.intro,True.intro⟩,⟨sg22829,True.intro,True.intro⟩⟩,⟨sg22832,⟨sg22831,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_75All : degreeTree39_75.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22804,degreeTree39_73All,degreeTree39_74All⟩

lemma degreeTree39_76All : degreeTree39_76.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22775,degreeTree39_72All,degreeTree39_75All⟩

lemma degreeTree39_77All : degreeTree39_77.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22717,degreeTree39_69All,degreeTree39_76All⟩

lemma degreeTree39_78All : degreeTree39_78.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22848,⟨sg22841,⟨sg22837,⟨sg22835,⟨sg22834,True.intro,True.intro⟩,⟨sg22836,True.intro,True.intro⟩⟩,⟨sg22839,⟨sg22838,True.intro,True.intro⟩,⟨sg22840,True.intro,True.intro⟩⟩⟩,⟨sg22845,⟨sg22843,⟨sg22842,True.intro,True.intro⟩,⟨sg22844,True.intro,True.intro⟩⟩,⟨sg22847,⟨sg22846,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22855,⟨sg22852,⟨sg22850,⟨sg22849,True.intro,True.intro⟩,⟨sg22851,True.intro,True.intro⟩⟩,⟨sg22854,⟨sg22853,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22859,⟨sg22857,⟨sg22856,True.intro,True.intro⟩,⟨sg22858,True.intro,True.intro⟩⟩,⟨sg22861,⟨sg22860,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_79All : degreeTree39_79.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22877,⟨sg22870,⟨sg22866,⟨sg22864,⟨sg22863,True.intro,True.intro⟩,⟨sg22865,True.intro,True.intro⟩⟩,⟨sg22868,⟨sg22867,True.intro,True.intro⟩,⟨sg22869,True.intro,True.intro⟩⟩⟩,⟨sg22874,⟨sg22872,⟨sg22871,True.intro,True.intro⟩,⟨sg22873,True.intro,True.intro⟩⟩,⟨sg22876,⟨sg22875,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22884,⟨sg22881,⟨sg22879,⟨sg22878,True.intro,True.intro⟩,⟨sg22880,True.intro,True.intro⟩⟩,⟨sg22883,⟨sg22882,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22888,⟨sg22886,⟨sg22885,True.intro,True.intro⟩,⟨sg22887,True.intro,True.intro⟩⟩,⟨sg22890,⟨sg22889,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_80All : degreeTree39_80.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22862,degreeTree39_78All,degreeTree39_79All⟩

lemma degreeTree39_81All : degreeTree39_81.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22906,⟨sg22899,⟨sg22895,⟨sg22893,⟨sg22892,True.intro,True.intro⟩,⟨sg22894,True.intro,True.intro⟩⟩,⟨sg22897,⟨sg22896,True.intro,True.intro⟩,⟨sg22898,True.intro,True.intro⟩⟩⟩,⟨sg22903,⟨sg22901,⟨sg22900,True.intro,True.intro⟩,⟨sg22902,True.intro,True.intro⟩⟩,⟨sg22905,⟨sg22904,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22913,⟨sg22910,⟨sg22908,⟨sg22907,True.intro,True.intro⟩,⟨sg22909,True.intro,True.intro⟩⟩,⟨sg22912,⟨sg22911,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22917,⟨sg22915,⟨sg22914,True.intro,True.intro⟩,⟨sg22916,True.intro,True.intro⟩⟩,⟨sg22919,⟨sg22918,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_82All : degreeTree39_82.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22935,⟨sg22928,⟨sg22924,⟨sg22922,⟨sg22921,True.intro,True.intro⟩,⟨sg22923,True.intro,True.intro⟩⟩,⟨sg22926,⟨sg22925,True.intro,True.intro⟩,⟨sg22927,True.intro,True.intro⟩⟩⟩,⟨sg22932,⟨sg22930,⟨sg22929,True.intro,True.intro⟩,⟨sg22931,True.intro,True.intro⟩⟩,⟨sg22934,⟨sg22933,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22942,⟨sg22939,⟨sg22937,⟨sg22936,True.intro,True.intro⟩,⟨sg22938,True.intro,True.intro⟩⟩,⟨sg22941,⟨sg22940,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22946,⟨sg22944,⟨sg22943,True.intro,True.intro⟩,⟨sg22945,True.intro,True.intro⟩⟩,⟨sg22948,⟨sg22947,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_83All : degreeTree39_83.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22920,degreeTree39_81All,degreeTree39_82All⟩

lemma degreeTree39_84All : degreeTree39_84.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22891,degreeTree39_80All,degreeTree39_83All⟩

lemma degreeTree39_85All : degreeTree39_85.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22964,⟨sg22957,⟨sg22953,⟨sg22951,⟨sg22950,True.intro,True.intro⟩,⟨sg22952,True.intro,True.intro⟩⟩,⟨sg22955,⟨sg22954,True.intro,True.intro⟩,⟨sg22956,True.intro,True.intro⟩⟩⟩,⟨sg22961,⟨sg22959,⟨sg22958,True.intro,True.intro⟩,⟨sg22960,True.intro,True.intro⟩⟩,⟨sg22963,⟨sg22962,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg22971,⟨sg22968,⟨sg22966,⟨sg22965,True.intro,True.intro⟩,⟨sg22967,True.intro,True.intro⟩⟩,⟨sg22970,⟨sg22969,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg22975,⟨sg22973,⟨sg22972,True.intro,True.intro⟩,⟨sg22974,True.intro,True.intro⟩⟩,⟨sg22977,⟨sg22976,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_86All : degreeTree39_86.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22993,⟨sg22986,⟨sg22982,⟨sg22980,⟨sg22979,True.intro,True.intro⟩,⟨sg22981,True.intro,True.intro⟩⟩,⟨sg22984,⟨sg22983,True.intro,True.intro⟩,⟨sg22985,True.intro,True.intro⟩⟩⟩,⟨sg22990,⟨sg22988,⟨sg22987,True.intro,True.intro⟩,⟨sg22989,True.intro,True.intro⟩⟩,⟨sg22992,⟨sg22991,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23000,⟨sg22997,⟨sg22995,⟨sg22994,True.intro,True.intro⟩,⟨sg22996,True.intro,True.intro⟩⟩,⟨sg22999,⟨sg22998,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23004,⟨sg23002,⟨sg23001,True.intro,True.intro⟩,⟨sg23003,True.intro,True.intro⟩⟩,⟨sg23006,⟨sg23005,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_87All : degreeTree39_87.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22978,degreeTree39_85All,degreeTree39_86All⟩

lemma degreeTree39_88All : degreeTree39_88.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23022,⟨sg23015,⟨sg23011,⟨sg23009,⟨sg23008,True.intro,True.intro⟩,⟨sg23010,True.intro,True.intro⟩⟩,⟨sg23013,⟨sg23012,True.intro,True.intro⟩,⟨sg23014,True.intro,True.intro⟩⟩⟩,⟨sg23019,⟨sg23017,⟨sg23016,True.intro,True.intro⟩,⟨sg23018,True.intro,True.intro⟩⟩,⟨sg23021,⟨sg23020,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23029,⟨sg23026,⟨sg23024,⟨sg23023,True.intro,True.intro⟩,⟨sg23025,True.intro,True.intro⟩⟩,⟨sg23028,⟨sg23027,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23033,⟨sg23031,⟨sg23030,True.intro,True.intro⟩,⟨sg23032,True.intro,True.intro⟩⟩,⟨sg23035,⟨sg23034,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_89All : degreeTree39_89.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23051,⟨sg23044,⟨sg23040,⟨sg23038,⟨sg23037,True.intro,True.intro⟩,⟨sg23039,True.intro,True.intro⟩⟩,⟨sg23042,⟨sg23041,True.intro,True.intro⟩,⟨sg23043,True.intro,True.intro⟩⟩⟩,⟨sg23048,⟨sg23046,⟨sg23045,True.intro,True.intro⟩,⟨sg23047,True.intro,True.intro⟩⟩,⟨sg23050,⟨sg23049,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23058,⟨sg23055,⟨sg23053,⟨sg23052,True.intro,True.intro⟩,⟨sg23054,True.intro,True.intro⟩⟩,⟨sg23057,⟨sg23056,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23062,⟨sg23060,⟨sg23059,True.intro,True.intro⟩,⟨sg23061,True.intro,True.intro⟩⟩,⟨sg23064,⟨sg23063,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_90All : degreeTree39_90.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23036,degreeTree39_88All,degreeTree39_89All⟩

lemma degreeTree39_91All : degreeTree39_91.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23007,degreeTree39_87All,degreeTree39_90All⟩

lemma degreeTree39_92All : degreeTree39_92.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22949,degreeTree39_84All,degreeTree39_91All⟩

lemma degreeTree39_93All : degreeTree39_93.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22833,degreeTree39_77All,degreeTree39_92All⟩

lemma degreeTree39_94All : degreeTree39_94.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23080,⟨sg23073,⟨sg23069,⟨sg23067,⟨sg23066,True.intro,True.intro⟩,⟨sg23068,True.intro,True.intro⟩⟩,⟨sg23071,⟨sg23070,True.intro,True.intro⟩,⟨sg23072,True.intro,True.intro⟩⟩⟩,⟨sg23077,⟨sg23075,⟨sg23074,True.intro,True.intro⟩,⟨sg23076,True.intro,True.intro⟩⟩,⟨sg23079,⟨sg23078,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23088,⟨sg23084,⟨sg23082,⟨sg23081,True.intro,True.intro⟩,⟨sg23083,True.intro,True.intro⟩⟩,⟨sg23086,⟨sg23085,True.intro,True.intro⟩,⟨sg23087,True.intro,True.intro⟩⟩⟩,⟨sg23092,⟨sg23090,⟨sg23089,True.intro,True.intro⟩,⟨sg23091,True.intro,True.intro⟩⟩,⟨sg23094,⟨sg23093,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_95All : degreeTree39_95.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23110,⟨sg23103,⟨sg23099,⟨sg23097,⟨sg23096,True.intro,True.intro⟩,⟨sg23098,True.intro,True.intro⟩⟩,⟨sg23101,⟨sg23100,True.intro,True.intro⟩,⟨sg23102,True.intro,True.intro⟩⟩⟩,⟨sg23107,⟨sg23105,⟨sg23104,True.intro,True.intro⟩,⟨sg23106,True.intro,True.intro⟩⟩,⟨sg23109,⟨sg23108,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23117,⟨sg23114,⟨sg23112,⟨sg23111,True.intro,True.intro⟩,⟨sg23113,True.intro,True.intro⟩⟩,⟨sg23116,⟨sg23115,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23121,⟨sg23119,⟨sg23118,True.intro,True.intro⟩,⟨sg23120,True.intro,True.intro⟩⟩,⟨sg23123,⟨sg23122,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_96All : degreeTree39_96.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23095,degreeTree39_94All,degreeTree39_95All⟩

lemma degreeTree39_97All : degreeTree39_97.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23139,⟨sg23132,⟨sg23128,⟨sg23126,⟨sg23125,True.intro,True.intro⟩,⟨sg23127,True.intro,True.intro⟩⟩,⟨sg23130,⟨sg23129,True.intro,True.intro⟩,⟨sg23131,True.intro,True.intro⟩⟩⟩,⟨sg23136,⟨sg23134,⟨sg23133,True.intro,True.intro⟩,⟨sg23135,True.intro,True.intro⟩⟩,⟨sg23138,⟨sg23137,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23146,⟨sg23143,⟨sg23141,⟨sg23140,True.intro,True.intro⟩,⟨sg23142,True.intro,True.intro⟩⟩,⟨sg23145,⟨sg23144,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23150,⟨sg23148,⟨sg23147,True.intro,True.intro⟩,⟨sg23149,True.intro,True.intro⟩⟩,⟨sg23152,⟨sg23151,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_98All : degreeTree39_98.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23168,⟨sg23161,⟨sg23157,⟨sg23155,⟨sg23154,True.intro,True.intro⟩,⟨sg23156,True.intro,True.intro⟩⟩,⟨sg23159,⟨sg23158,True.intro,True.intro⟩,⟨sg23160,True.intro,True.intro⟩⟩⟩,⟨sg23165,⟨sg23163,⟨sg23162,True.intro,True.intro⟩,⟨sg23164,True.intro,True.intro⟩⟩,⟨sg23167,⟨sg23166,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23175,⟨sg23172,⟨sg23170,⟨sg23169,True.intro,True.intro⟩,⟨sg23171,True.intro,True.intro⟩⟩,⟨sg23174,⟨sg23173,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23179,⟨sg23177,⟨sg23176,True.intro,True.intro⟩,⟨sg23178,True.intro,True.intro⟩⟩,⟨sg23181,⟨sg23180,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_99All : degreeTree39_99.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23153,degreeTree39_97All,degreeTree39_98All⟩

lemma degreeTree39_100All : degreeTree39_100.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23124,degreeTree39_96All,degreeTree39_99All⟩

lemma degreeTree39_101All : degreeTree39_101.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23197,⟨sg23190,⟨sg23186,⟨sg23184,⟨sg23183,True.intro,True.intro⟩,⟨sg23185,True.intro,True.intro⟩⟩,⟨sg23188,⟨sg23187,True.intro,True.intro⟩,⟨sg23189,True.intro,True.intro⟩⟩⟩,⟨sg23194,⟨sg23192,⟨sg23191,True.intro,True.intro⟩,⟨sg23193,True.intro,True.intro⟩⟩,⟨sg23196,⟨sg23195,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23204,⟨sg23201,⟨sg23199,⟨sg23198,True.intro,True.intro⟩,⟨sg23200,True.intro,True.intro⟩⟩,⟨sg23203,⟨sg23202,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23208,⟨sg23206,⟨sg23205,True.intro,True.intro⟩,⟨sg23207,True.intro,True.intro⟩⟩,⟨sg23210,⟨sg23209,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_102All : degreeTree39_102.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23226,⟨sg23219,⟨sg23215,⟨sg23213,⟨sg23212,True.intro,True.intro⟩,⟨sg23214,True.intro,True.intro⟩⟩,⟨sg23217,⟨sg23216,True.intro,True.intro⟩,⟨sg23218,True.intro,True.intro⟩⟩⟩,⟨sg23223,⟨sg23221,⟨sg23220,True.intro,True.intro⟩,⟨sg23222,True.intro,True.intro⟩⟩,⟨sg23225,⟨sg23224,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23233,⟨sg23230,⟨sg23228,⟨sg23227,True.intro,True.intro⟩,⟨sg23229,True.intro,True.intro⟩⟩,⟨sg23232,⟨sg23231,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23237,⟨sg23235,⟨sg23234,True.intro,True.intro⟩,⟨sg23236,True.intro,True.intro⟩⟩,⟨sg23239,⟨sg23238,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_103All : degreeTree39_103.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23211,degreeTree39_101All,degreeTree39_102All⟩

lemma degreeTree39_104All : degreeTree39_104.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23255,⟨sg23248,⟨sg23244,⟨sg23242,⟨sg23241,True.intro,True.intro⟩,⟨sg23243,True.intro,True.intro⟩⟩,⟨sg23246,⟨sg23245,True.intro,True.intro⟩,⟨sg23247,True.intro,True.intro⟩⟩⟩,⟨sg23252,⟨sg23250,⟨sg23249,True.intro,True.intro⟩,⟨sg23251,True.intro,True.intro⟩⟩,⟨sg23254,⟨sg23253,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23262,⟨sg23259,⟨sg23257,⟨sg23256,True.intro,True.intro⟩,⟨sg23258,True.intro,True.intro⟩⟩,⟨sg23261,⟨sg23260,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23266,⟨sg23264,⟨sg23263,True.intro,True.intro⟩,⟨sg23265,True.intro,True.intro⟩⟩,⟨sg23268,⟨sg23267,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_105All : degreeTree39_105.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23284,⟨sg23277,⟨sg23273,⟨sg23271,⟨sg23270,True.intro,True.intro⟩,⟨sg23272,True.intro,True.intro⟩⟩,⟨sg23275,⟨sg23274,True.intro,True.intro⟩,⟨sg23276,True.intro,True.intro⟩⟩⟩,⟨sg23281,⟨sg23279,⟨sg23278,True.intro,True.intro⟩,⟨sg23280,True.intro,True.intro⟩⟩,⟨sg23283,⟨sg23282,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23291,⟨sg23288,⟨sg23286,⟨sg23285,True.intro,True.intro⟩,⟨sg23287,True.intro,True.intro⟩⟩,⟨sg23290,⟨sg23289,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23295,⟨sg23293,⟨sg23292,True.intro,True.intro⟩,⟨sg23294,True.intro,True.intro⟩⟩,⟨sg23297,⟨sg23296,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_106All : degreeTree39_106.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23269,degreeTree39_104All,degreeTree39_105All⟩

lemma degreeTree39_107All : degreeTree39_107.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23240,degreeTree39_103All,degreeTree39_106All⟩

lemma degreeTree39_108All : degreeTree39_108.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23182,degreeTree39_100All,degreeTree39_107All⟩

lemma degreeTree39_109All : degreeTree39_109.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23313,⟨sg23306,⟨sg23302,⟨sg23300,⟨sg23299,True.intro,True.intro⟩,⟨sg23301,True.intro,True.intro⟩⟩,⟨sg23304,⟨sg23303,True.intro,True.intro⟩,⟨sg23305,True.intro,True.intro⟩⟩⟩,⟨sg23310,⟨sg23308,⟨sg23307,True.intro,True.intro⟩,⟨sg23309,True.intro,True.intro⟩⟩,⟨sg23312,⟨sg23311,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23320,⟨sg23317,⟨sg23315,⟨sg23314,True.intro,True.intro⟩,⟨sg23316,True.intro,True.intro⟩⟩,⟨sg23319,⟨sg23318,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23324,⟨sg23322,⟨sg23321,True.intro,True.intro⟩,⟨sg23323,True.intro,True.intro⟩⟩,⟨sg23326,⟨sg23325,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_110All : degreeTree39_110.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23342,⟨sg23335,⟨sg23331,⟨sg23329,⟨sg23328,True.intro,True.intro⟩,⟨sg23330,True.intro,True.intro⟩⟩,⟨sg23333,⟨sg23332,True.intro,True.intro⟩,⟨sg23334,True.intro,True.intro⟩⟩⟩,⟨sg23339,⟨sg23337,⟨sg23336,True.intro,True.intro⟩,⟨sg23338,True.intro,True.intro⟩⟩,⟨sg23341,⟨sg23340,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23349,⟨sg23346,⟨sg23344,⟨sg23343,True.intro,True.intro⟩,⟨sg23345,True.intro,True.intro⟩⟩,⟨sg23348,⟨sg23347,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23353,⟨sg23351,⟨sg23350,True.intro,True.intro⟩,⟨sg23352,True.intro,True.intro⟩⟩,⟨sg23355,⟨sg23354,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_111All : degreeTree39_111.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23327,degreeTree39_109All,degreeTree39_110All⟩

lemma degreeTree39_112All : degreeTree39_112.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23371,⟨sg23364,⟨sg23360,⟨sg23358,⟨sg23357,True.intro,True.intro⟩,⟨sg23359,True.intro,True.intro⟩⟩,⟨sg23362,⟨sg23361,True.intro,True.intro⟩,⟨sg23363,True.intro,True.intro⟩⟩⟩,⟨sg23368,⟨sg23366,⟨sg23365,True.intro,True.intro⟩,⟨sg23367,True.intro,True.intro⟩⟩,⟨sg23370,⟨sg23369,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23378,⟨sg23375,⟨sg23373,⟨sg23372,True.intro,True.intro⟩,⟨sg23374,True.intro,True.intro⟩⟩,⟨sg23377,⟨sg23376,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23382,⟨sg23380,⟨sg23379,True.intro,True.intro⟩,⟨sg23381,True.intro,True.intro⟩⟩,⟨sg23384,⟨sg23383,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_113All : degreeTree39_113.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23400,⟨sg23393,⟨sg23389,⟨sg23387,⟨sg23386,True.intro,True.intro⟩,⟨sg23388,True.intro,True.intro⟩⟩,⟨sg23391,⟨sg23390,True.intro,True.intro⟩,⟨sg23392,True.intro,True.intro⟩⟩⟩,⟨sg23397,⟨sg23395,⟨sg23394,True.intro,True.intro⟩,⟨sg23396,True.intro,True.intro⟩⟩,⟨sg23399,⟨sg23398,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23407,⟨sg23404,⟨sg23402,⟨sg23401,True.intro,True.intro⟩,⟨sg23403,True.intro,True.intro⟩⟩,⟨sg23406,⟨sg23405,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23411,⟨sg23409,⟨sg23408,True.intro,True.intro⟩,⟨sg23410,True.intro,True.intro⟩⟩,⟨sg23413,⟨sg23412,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_114All : degreeTree39_114.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23385,degreeTree39_112All,degreeTree39_113All⟩

lemma degreeTree39_115All : degreeTree39_115.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23356,degreeTree39_111All,degreeTree39_114All⟩

lemma degreeTree39_116All : degreeTree39_116.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23429,⟨sg23422,⟨sg23418,⟨sg23416,⟨sg23415,True.intro,True.intro⟩,⟨sg23417,True.intro,True.intro⟩⟩,⟨sg23420,⟨sg23419,True.intro,True.intro⟩,⟨sg23421,True.intro,True.intro⟩⟩⟩,⟨sg23426,⟨sg23424,⟨sg23423,True.intro,True.intro⟩,⟨sg23425,True.intro,True.intro⟩⟩,⟨sg23428,⟨sg23427,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23436,⟨sg23433,⟨sg23431,⟨sg23430,True.intro,True.intro⟩,⟨sg23432,True.intro,True.intro⟩⟩,⟨sg23435,⟨sg23434,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23440,⟨sg23438,⟨sg23437,True.intro,True.intro⟩,⟨sg23439,True.intro,True.intro⟩⟩,⟨sg23442,⟨sg23441,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_117All : degreeTree39_117.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23458,⟨sg23451,⟨sg23447,⟨sg23445,⟨sg23444,True.intro,True.intro⟩,⟨sg23446,True.intro,True.intro⟩⟩,⟨sg23449,⟨sg23448,True.intro,True.intro⟩,⟨sg23450,True.intro,True.intro⟩⟩⟩,⟨sg23455,⟨sg23453,⟨sg23452,True.intro,True.intro⟩,⟨sg23454,True.intro,True.intro⟩⟩,⟨sg23457,⟨sg23456,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23465,⟨sg23462,⟨sg23460,⟨sg23459,True.intro,True.intro⟩,⟨sg23461,True.intro,True.intro⟩⟩,⟨sg23464,⟨sg23463,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23469,⟨sg23467,⟨sg23466,True.intro,True.intro⟩,⟨sg23468,True.intro,True.intro⟩⟩,⟨sg23471,⟨sg23470,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_118All : degreeTree39_118.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23443,degreeTree39_116All,degreeTree39_117All⟩

lemma degreeTree39_119All : degreeTree39_119.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23487,⟨sg23480,⟨sg23476,⟨sg23474,⟨sg23473,True.intro,True.intro⟩,⟨sg23475,True.intro,True.intro⟩⟩,⟨sg23478,⟨sg23477,True.intro,True.intro⟩,⟨sg23479,True.intro,True.intro⟩⟩⟩,⟨sg23484,⟨sg23482,⟨sg23481,True.intro,True.intro⟩,⟨sg23483,True.intro,True.intro⟩⟩,⟨sg23486,⟨sg23485,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23494,⟨sg23491,⟨sg23489,⟨sg23488,True.intro,True.intro⟩,⟨sg23490,True.intro,True.intro⟩⟩,⟨sg23493,⟨sg23492,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23498,⟨sg23496,⟨sg23495,True.intro,True.intro⟩,⟨sg23497,True.intro,True.intro⟩⟩,⟨sg23500,⟨sg23499,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_120All : degreeTree39_120.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23516,⟨sg23509,⟨sg23505,⟨sg23503,⟨sg23502,True.intro,True.intro⟩,⟨sg23504,True.intro,True.intro⟩⟩,⟨sg23507,⟨sg23506,True.intro,True.intro⟩,⟨sg23508,True.intro,True.intro⟩⟩⟩,⟨sg23513,⟨sg23511,⟨sg23510,True.intro,True.intro⟩,⟨sg23512,True.intro,True.intro⟩⟩,⟨sg23515,⟨sg23514,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg23523,⟨sg23520,⟨sg23518,⟨sg23517,True.intro,True.intro⟩,⟨sg23519,True.intro,True.intro⟩⟩,⟨sg23522,⟨sg23521,True.intro,True.intro⟩,True.intro⟩⟩,⟨sg23527,⟨sg23525,⟨sg23524,True.intro,True.intro⟩,⟨sg23526,True.intro,True.intro⟩⟩,⟨sg23529,⟨sg23528,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree39_121All : degreeTree39_121.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23501,degreeTree39_119All,degreeTree39_120All⟩

lemma degreeTree39_122All : degreeTree39_122.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23472,degreeTree39_118All,degreeTree39_121All⟩

lemma degreeTree39_123All : degreeTree39_123.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23414,degreeTree39_115All,degreeTree39_122All⟩

lemma degreeTree39_124All : degreeTree39_124.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23298,degreeTree39_108All,degreeTree39_123All⟩

lemma degreeTree39_125All : degreeTree39_125.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg23065,degreeTree39_93All,degreeTree39_124All⟩

lemma degreeTree39_126All : degreeTree39_126.All (RowSquare [11,9,4,3,2,2,2,2,2,1,1]) := by
  exact ⟨sg22600,degreeTree39_62All,degreeTree39_125All⟩

lemma degreeTreeAll39 : degreeTree39.All
    (fun rs => SquareOccurs (candidate 6 4 1) (rowDiagram rs)) := by
  have hp : rowDiagram [11,9,4,3,2,2,2,2,2,1,1] = candidate 6 4 1 := rowDiagram_candidate (M := 6) (b := 4) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree39_126All

end UniversalTensorSquare
end
end

end OAI
