import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData43
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes58
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes59
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes60
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes61
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes62
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes63
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes64
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes65
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes66
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes67
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes68
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes69
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes70
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes71
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes72
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes73
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes74
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes75
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes76
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes77
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes78

namespace OAI

/-! Degree Tree Proof 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree43_0All : degreeTree43_0.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23683,⟨sg23679,⟨sg23677,⟨sg23676,⟨sg23675,True.intro,True.intro⟩,True.intro⟩,⟨sg23678,True.intro,True.intro⟩⟩,⟨sg23681,⟨sg23680,True.intro,True.intro⟩,⟨sg23682,True.intro,True.intro⟩⟩⟩,⟨sg23687,⟨sg23685,⟨sg23684,True.intro,True.intro⟩,⟨sg23686,True.intro,True.intro⟩⟩,⟨sg23689,⟨sg23688,True.intro,True.intro⟩,⟨sg23690,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_1All : degreeTree43_1.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23699,⟨sg23695,⟨sg23693,⟨sg23692,True.intro,True.intro⟩,⟨sg23694,True.intro,True.intro⟩⟩,⟨sg23697,⟨sg23696,True.intro,True.intro⟩,⟨sg23698,True.intro,True.intro⟩⟩⟩,⟨sg23703,⟨sg23701,⟨sg23700,True.intro,True.intro⟩,⟨sg23702,True.intro,True.intro⟩⟩,⟨sg23705,⟨sg23704,True.intro,True.intro⟩,⟨sg23706,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_2All : degreeTree43_2.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23691,degreeTree43_0All,degreeTree43_1All⟩

lemma degreeTree43_3All : degreeTree43_3.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23723,⟨sg23715,⟨sg23711,⟨sg23709,⟨sg23708,True.intro,True.intro⟩,⟨sg23710,True.intro,True.intro⟩⟩,⟨sg23713,⟨sg23712,True.intro,True.intro⟩,⟨sg23714,True.intro,True.intro⟩⟩⟩,⟨sg23719,⟨sg23717,⟨sg23716,True.intro,True.intro⟩,⟨sg23718,True.intro,True.intro⟩⟩,⟨sg23721,⟨sg23720,True.intro,True.intro⟩,⟨sg23722,True.intro,True.intro⟩⟩⟩⟩,⟨sg23731,⟨sg23727,⟨sg23725,⟨sg23724,True.intro,True.intro⟩,⟨sg23726,True.intro,True.intro⟩⟩,⟨sg23729,⟨sg23728,True.intro,True.intro⟩,⟨sg23730,True.intro,True.intro⟩⟩⟩,⟨sg23735,⟨sg23733,⟨sg23732,True.intro,True.intro⟩,⟨sg23734,True.intro,True.intro⟩⟩,⟨sg23737,⟨sg23736,True.intro,True.intro⟩,⟨sg23738,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_4All : degreeTree43_4.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23707,degreeTree43_2All,degreeTree43_3All⟩

lemma degreeTree43_5All : degreeTree43_5.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23748,⟨sg23744,⟨sg23742,⟨sg23741,⟨sg23740,True.intro,True.intro⟩,True.intro⟩,⟨sg23743,True.intro,True.intro⟩⟩,⟨sg23746,⟨sg23745,True.intro,True.intro⟩,⟨sg23747,True.intro,True.intro⟩⟩⟩,⟨sg23752,⟨sg23750,⟨sg23749,True.intro,True.intro⟩,⟨sg23751,True.intro,True.intro⟩⟩,⟨sg23754,⟨sg23753,True.intro,True.intro⟩,⟨sg23755,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_6All : degreeTree43_6.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23764,⟨sg23760,⟨sg23758,⟨sg23757,True.intro,True.intro⟩,⟨sg23759,True.intro,True.intro⟩⟩,⟨sg23762,⟨sg23761,True.intro,True.intro⟩,⟨sg23763,True.intro,True.intro⟩⟩⟩,⟨sg23768,⟨sg23766,⟨sg23765,True.intro,True.intro⟩,⟨sg23767,True.intro,True.intro⟩⟩,⟨sg23770,⟨sg23769,True.intro,True.intro⟩,⟨sg23771,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_7All : degreeTree43_7.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23756,degreeTree43_5All,degreeTree43_6All⟩

lemma degreeTree43_8All : degreeTree43_8.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23788,⟨sg23780,⟨sg23776,⟨sg23774,⟨sg23773,True.intro,True.intro⟩,⟨sg23775,True.intro,True.intro⟩⟩,⟨sg23778,⟨sg23777,True.intro,True.intro⟩,⟨sg23779,True.intro,True.intro⟩⟩⟩,⟨sg23784,⟨sg23782,⟨sg23781,True.intro,True.intro⟩,⟨sg23783,True.intro,True.intro⟩⟩,⟨sg23786,⟨sg23785,True.intro,True.intro⟩,⟨sg23787,True.intro,True.intro⟩⟩⟩⟩,⟨sg23796,⟨sg23792,⟨sg23790,⟨sg23789,True.intro,True.intro⟩,⟨sg23791,True.intro,True.intro⟩⟩,⟨sg23794,⟨sg23793,True.intro,True.intro⟩,⟨sg23795,True.intro,True.intro⟩⟩⟩,⟨sg23800,⟨sg23798,⟨sg23797,True.intro,True.intro⟩,⟨sg23799,True.intro,True.intro⟩⟩,⟨sg23802,⟨sg23801,True.intro,True.intro⟩,⟨sg23803,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_9All : degreeTree43_9.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23772,degreeTree43_7All,degreeTree43_8All⟩

lemma degreeTree43_10All : degreeTree43_10.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23739,degreeTree43_4All,degreeTree43_9All⟩

lemma degreeTree43_11All : degreeTree43_11.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23813,⟨sg23809,⟨sg23807,⟨sg23806,⟨sg23805,True.intro,True.intro⟩,True.intro⟩,⟨sg23808,True.intro,True.intro⟩⟩,⟨sg23811,⟨sg23810,True.intro,True.intro⟩,⟨sg23812,True.intro,True.intro⟩⟩⟩,⟨sg23817,⟨sg23815,⟨sg23814,True.intro,True.intro⟩,⟨sg23816,True.intro,True.intro⟩⟩,⟨sg23819,⟨sg23818,True.intro,True.intro⟩,⟨sg23820,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_12All : degreeTree43_12.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23829,⟨sg23825,⟨sg23823,⟨sg23822,True.intro,True.intro⟩,⟨sg23824,True.intro,True.intro⟩⟩,⟨sg23827,⟨sg23826,True.intro,True.intro⟩,⟨sg23828,True.intro,True.intro⟩⟩⟩,⟨sg23833,⟨sg23831,⟨sg23830,True.intro,True.intro⟩,⟨sg23832,True.intro,True.intro⟩⟩,⟨sg23835,⟨sg23834,True.intro,True.intro⟩,⟨sg23836,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_13All : degreeTree43_13.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23821,degreeTree43_11All,degreeTree43_12All⟩

lemma degreeTree43_14All : degreeTree43_14.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23853,⟨sg23845,⟨sg23841,⟨sg23839,⟨sg23838,True.intro,True.intro⟩,⟨sg23840,True.intro,True.intro⟩⟩,⟨sg23843,⟨sg23842,True.intro,True.intro⟩,⟨sg23844,True.intro,True.intro⟩⟩⟩,⟨sg23849,⟨sg23847,⟨sg23846,True.intro,True.intro⟩,⟨sg23848,True.intro,True.intro⟩⟩,⟨sg23851,⟨sg23850,True.intro,True.intro⟩,⟨sg23852,True.intro,True.intro⟩⟩⟩⟩,⟨sg23861,⟨sg23857,⟨sg23855,⟨sg23854,True.intro,True.intro⟩,⟨sg23856,True.intro,True.intro⟩⟩,⟨sg23859,⟨sg23858,True.intro,True.intro⟩,⟨sg23860,True.intro,True.intro⟩⟩⟩,⟨sg23865,⟨sg23863,⟨sg23862,True.intro,True.intro⟩,⟨sg23864,True.intro,True.intro⟩⟩,⟨sg23867,⟨sg23866,True.intro,True.intro⟩,⟨sg23868,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_15All : degreeTree43_15.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23837,degreeTree43_13All,degreeTree43_14All⟩

lemma degreeTree43_16All : degreeTree43_16.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23885,⟨sg23877,⟨sg23873,⟨sg23871,⟨sg23870,True.intro,True.intro⟩,⟨sg23872,True.intro,True.intro⟩⟩,⟨sg23875,⟨sg23874,True.intro,True.intro⟩,⟨sg23876,True.intro,True.intro⟩⟩⟩,⟨sg23881,⟨sg23879,⟨sg23878,True.intro,True.intro⟩,⟨sg23880,True.intro,True.intro⟩⟩,⟨sg23883,⟨sg23882,True.intro,True.intro⟩,⟨sg23884,True.intro,True.intro⟩⟩⟩⟩,⟨sg23893,⟨sg23889,⟨sg23887,⟨sg23886,True.intro,True.intro⟩,⟨sg23888,True.intro,True.intro⟩⟩,⟨sg23891,⟨sg23890,True.intro,True.intro⟩,⟨sg23892,True.intro,True.intro⟩⟩⟩,⟨sg23897,⟨sg23895,⟨sg23894,True.intro,True.intro⟩,⟨sg23896,True.intro,True.intro⟩⟩,⟨sg23899,⟨sg23898,True.intro,True.intro⟩,⟨sg23900,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_17All : degreeTree43_17.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23917,⟨sg23909,⟨sg23905,⟨sg23903,⟨sg23902,True.intro,True.intro⟩,⟨sg23904,True.intro,True.intro⟩⟩,⟨sg23907,⟨sg23906,True.intro,True.intro⟩,⟨sg23908,True.intro,True.intro⟩⟩⟩,⟨sg23913,⟨sg23911,⟨sg23910,True.intro,True.intro⟩,⟨sg23912,True.intro,True.intro⟩⟩,⟨sg23915,⟨sg23914,True.intro,True.intro⟩,⟨sg23916,True.intro,True.intro⟩⟩⟩⟩,⟨sg23925,⟨sg23921,⟨sg23919,⟨sg23918,True.intro,True.intro⟩,⟨sg23920,True.intro,True.intro⟩⟩,⟨sg23923,⟨sg23922,True.intro,True.intro⟩,⟨sg23924,True.intro,True.intro⟩⟩⟩,⟨sg23929,⟨sg23927,⟨sg23926,True.intro,True.intro⟩,⟨sg23928,True.intro,True.intro⟩⟩,⟨sg23931,⟨sg23930,True.intro,True.intro⟩,⟨sg23932,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_18All : degreeTree43_18.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23901,degreeTree43_16All,degreeTree43_17All⟩

lemma degreeTree43_19All : degreeTree43_19.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23869,degreeTree43_15All,degreeTree43_18All⟩

lemma degreeTree43_20All : degreeTree43_20.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23804,degreeTree43_10All,degreeTree43_19All⟩

lemma degreeTree43_21All : degreeTree43_21.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23942,⟨sg23938,⟨sg23936,⟨sg23935,⟨sg23934,True.intro,True.intro⟩,True.intro⟩,⟨sg23937,True.intro,True.intro⟩⟩,⟨sg23940,⟨sg23939,True.intro,True.intro⟩,⟨sg23941,True.intro,True.intro⟩⟩⟩,⟨sg23946,⟨sg23944,⟨sg23943,True.intro,True.intro⟩,⟨sg23945,True.intro,True.intro⟩⟩,⟨sg23948,⟨sg23947,True.intro,True.intro⟩,⟨sg23949,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_22All : degreeTree43_22.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23958,⟨sg23954,⟨sg23952,⟨sg23951,True.intro,True.intro⟩,⟨sg23953,True.intro,True.intro⟩⟩,⟨sg23956,⟨sg23955,True.intro,True.intro⟩,⟨sg23957,True.intro,True.intro⟩⟩⟩,⟨sg23962,⟨sg23960,⟨sg23959,True.intro,True.intro⟩,⟨sg23961,True.intro,True.intro⟩⟩,⟨sg23964,⟨sg23963,True.intro,True.intro⟩,⟨sg23965,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_23All : degreeTree43_23.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23950,degreeTree43_21All,degreeTree43_22All⟩

lemma degreeTree43_24All : degreeTree43_24.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23982,⟨sg23974,⟨sg23970,⟨sg23968,⟨sg23967,True.intro,True.intro⟩,⟨sg23969,True.intro,True.intro⟩⟩,⟨sg23972,⟨sg23971,True.intro,True.intro⟩,⟨sg23973,True.intro,True.intro⟩⟩⟩,⟨sg23978,⟨sg23976,⟨sg23975,True.intro,True.intro⟩,⟨sg23977,True.intro,True.intro⟩⟩,⟨sg23980,⟨sg23979,True.intro,True.intro⟩,⟨sg23981,True.intro,True.intro⟩⟩⟩⟩,⟨sg23990,⟨sg23986,⟨sg23984,⟨sg23983,True.intro,True.intro⟩,⟨sg23985,True.intro,True.intro⟩⟩,⟨sg23988,⟨sg23987,True.intro,True.intro⟩,⟨sg23989,True.intro,True.intro⟩⟩⟩,⟨sg23994,⟨sg23992,⟨sg23991,True.intro,True.intro⟩,⟨sg23993,True.intro,True.intro⟩⟩,⟨sg23996,⟨sg23995,True.intro,True.intro⟩,⟨sg23997,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_25All : degreeTree43_25.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23966,degreeTree43_23All,degreeTree43_24All⟩

lemma degreeTree43_26All : degreeTree43_26.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24014,⟨sg24006,⟨sg24002,⟨sg24000,⟨sg23999,True.intro,True.intro⟩,⟨sg24001,True.intro,True.intro⟩⟩,⟨sg24004,⟨sg24003,True.intro,True.intro⟩,⟨sg24005,True.intro,True.intro⟩⟩⟩,⟨sg24010,⟨sg24008,⟨sg24007,True.intro,True.intro⟩,⟨sg24009,True.intro,True.intro⟩⟩,⟨sg24012,⟨sg24011,True.intro,True.intro⟩,⟨sg24013,True.intro,True.intro⟩⟩⟩⟩,⟨sg24022,⟨sg24018,⟨sg24016,⟨sg24015,True.intro,True.intro⟩,⟨sg24017,True.intro,True.intro⟩⟩,⟨sg24020,⟨sg24019,True.intro,True.intro⟩,⟨sg24021,True.intro,True.intro⟩⟩⟩,⟨sg24026,⟨sg24024,⟨sg24023,True.intro,True.intro⟩,⟨sg24025,True.intro,True.intro⟩⟩,⟨sg24028,⟨sg24027,True.intro,True.intro⟩,⟨sg24029,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_27All : degreeTree43_27.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24046,⟨sg24038,⟨sg24034,⟨sg24032,⟨sg24031,True.intro,True.intro⟩,⟨sg24033,True.intro,True.intro⟩⟩,⟨sg24036,⟨sg24035,True.intro,True.intro⟩,⟨sg24037,True.intro,True.intro⟩⟩⟩,⟨sg24042,⟨sg24040,⟨sg24039,True.intro,True.intro⟩,⟨sg24041,True.intro,True.intro⟩⟩,⟨sg24044,⟨sg24043,True.intro,True.intro⟩,⟨sg24045,True.intro,True.intro⟩⟩⟩⟩,⟨sg24054,⟨sg24050,⟨sg24048,⟨sg24047,True.intro,True.intro⟩,⟨sg24049,True.intro,True.intro⟩⟩,⟨sg24052,⟨sg24051,True.intro,True.intro⟩,⟨sg24053,True.intro,True.intro⟩⟩⟩,⟨sg24058,⟨sg24056,⟨sg24055,True.intro,True.intro⟩,⟨sg24057,True.intro,True.intro⟩⟩,⟨sg24060,⟨sg24059,True.intro,True.intro⟩,⟨sg24061,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_28All : degreeTree43_28.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24030,degreeTree43_26All,degreeTree43_27All⟩

lemma degreeTree43_29All : degreeTree43_29.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23998,degreeTree43_25All,degreeTree43_28All⟩

lemma degreeTree43_30All : degreeTree43_30.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24071,⟨sg24067,⟨sg24065,⟨sg24064,⟨sg24063,True.intro,True.intro⟩,True.intro⟩,⟨sg24066,True.intro,True.intro⟩⟩,⟨sg24069,⟨sg24068,True.intro,True.intro⟩,⟨sg24070,True.intro,True.intro⟩⟩⟩,⟨sg24075,⟨sg24073,⟨sg24072,True.intro,True.intro⟩,⟨sg24074,True.intro,True.intro⟩⟩,⟨sg24077,⟨sg24076,True.intro,True.intro⟩,⟨sg24078,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_31All : degreeTree43_31.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24087,⟨sg24083,⟨sg24081,⟨sg24080,True.intro,True.intro⟩,⟨sg24082,True.intro,True.intro⟩⟩,⟨sg24085,⟨sg24084,True.intro,True.intro⟩,⟨sg24086,True.intro,True.intro⟩⟩⟩,⟨sg24091,⟨sg24089,⟨sg24088,True.intro,True.intro⟩,⟨sg24090,True.intro,True.intro⟩⟩,⟨sg24093,⟨sg24092,True.intro,True.intro⟩,⟨sg24094,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_32All : degreeTree43_32.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24079,degreeTree43_30All,degreeTree43_31All⟩

lemma degreeTree43_33All : degreeTree43_33.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24111,⟨sg24103,⟨sg24099,⟨sg24097,⟨sg24096,True.intro,True.intro⟩,⟨sg24098,True.intro,True.intro⟩⟩,⟨sg24101,⟨sg24100,True.intro,True.intro⟩,⟨sg24102,True.intro,True.intro⟩⟩⟩,⟨sg24107,⟨sg24105,⟨sg24104,True.intro,True.intro⟩,⟨sg24106,True.intro,True.intro⟩⟩,⟨sg24109,⟨sg24108,True.intro,True.intro⟩,⟨sg24110,True.intro,True.intro⟩⟩⟩⟩,⟨sg24119,⟨sg24115,⟨sg24113,⟨sg24112,True.intro,True.intro⟩,⟨sg24114,True.intro,True.intro⟩⟩,⟨sg24117,⟨sg24116,True.intro,True.intro⟩,⟨sg24118,True.intro,True.intro⟩⟩⟩,⟨sg24123,⟨sg24121,⟨sg24120,True.intro,True.intro⟩,⟨sg24122,True.intro,True.intro⟩⟩,⟨sg24125,⟨sg24124,True.intro,True.intro⟩,⟨sg24126,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_34All : degreeTree43_34.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24095,degreeTree43_32All,degreeTree43_33All⟩

lemma degreeTree43_35All : degreeTree43_35.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24143,⟨sg24135,⟨sg24131,⟨sg24129,⟨sg24128,True.intro,True.intro⟩,⟨sg24130,True.intro,True.intro⟩⟩,⟨sg24133,⟨sg24132,True.intro,True.intro⟩,⟨sg24134,True.intro,True.intro⟩⟩⟩,⟨sg24139,⟨sg24137,⟨sg24136,True.intro,True.intro⟩,⟨sg24138,True.intro,True.intro⟩⟩,⟨sg24141,⟨sg24140,True.intro,True.intro⟩,⟨sg24142,True.intro,True.intro⟩⟩⟩⟩,⟨sg24151,⟨sg24147,⟨sg24145,⟨sg24144,True.intro,True.intro⟩,⟨sg24146,True.intro,True.intro⟩⟩,⟨sg24149,⟨sg24148,True.intro,True.intro⟩,⟨sg24150,True.intro,True.intro⟩⟩⟩,⟨sg24155,⟨sg24153,⟨sg24152,True.intro,True.intro⟩,⟨sg24154,True.intro,True.intro⟩⟩,⟨sg24157,⟨sg24156,True.intro,True.intro⟩,⟨sg24158,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_36All : degreeTree43_36.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24175,⟨sg24167,⟨sg24163,⟨sg24161,⟨sg24160,True.intro,True.intro⟩,⟨sg24162,True.intro,True.intro⟩⟩,⟨sg24165,⟨sg24164,True.intro,True.intro⟩,⟨sg24166,True.intro,True.intro⟩⟩⟩,⟨sg24171,⟨sg24169,⟨sg24168,True.intro,True.intro⟩,⟨sg24170,True.intro,True.intro⟩⟩,⟨sg24173,⟨sg24172,True.intro,True.intro⟩,⟨sg24174,True.intro,True.intro⟩⟩⟩⟩,⟨sg24183,⟨sg24179,⟨sg24177,⟨sg24176,True.intro,True.intro⟩,⟨sg24178,True.intro,True.intro⟩⟩,⟨sg24181,⟨sg24180,True.intro,True.intro⟩,⟨sg24182,True.intro,True.intro⟩⟩⟩,⟨sg24187,⟨sg24185,⟨sg24184,True.intro,True.intro⟩,⟨sg24186,True.intro,True.intro⟩⟩,⟨sg24189,⟨sg24188,True.intro,True.intro⟩,⟨sg24190,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_37All : degreeTree43_37.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24159,degreeTree43_35All,degreeTree43_36All⟩

lemma degreeTree43_38All : degreeTree43_38.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24127,degreeTree43_34All,degreeTree43_37All⟩

lemma degreeTree43_39All : degreeTree43_39.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24062,degreeTree43_29All,degreeTree43_38All⟩

lemma degreeTree43_40All : degreeTree43_40.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg23933,degreeTree43_20All,degreeTree43_39All⟩

lemma degreeTree43_41All : degreeTree43_41.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24200,⟨sg24196,⟨sg24194,⟨sg24193,⟨sg24192,True.intro,True.intro⟩,True.intro⟩,⟨sg24195,True.intro,True.intro⟩⟩,⟨sg24198,⟨sg24197,True.intro,True.intro⟩,⟨sg24199,True.intro,True.intro⟩⟩⟩,⟨sg24204,⟨sg24202,⟨sg24201,True.intro,True.intro⟩,⟨sg24203,True.intro,True.intro⟩⟩,⟨sg24206,⟨sg24205,True.intro,True.intro⟩,⟨sg24207,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_42All : degreeTree43_42.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24216,⟨sg24212,⟨sg24210,⟨sg24209,True.intro,True.intro⟩,⟨sg24211,True.intro,True.intro⟩⟩,⟨sg24214,⟨sg24213,True.intro,True.intro⟩,⟨sg24215,True.intro,True.intro⟩⟩⟩,⟨sg24220,⟨sg24218,⟨sg24217,True.intro,True.intro⟩,⟨sg24219,True.intro,True.intro⟩⟩,⟨sg24222,⟨sg24221,True.intro,True.intro⟩,⟨sg24223,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_43All : degreeTree43_43.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24208,degreeTree43_41All,degreeTree43_42All⟩

lemma degreeTree43_44All : degreeTree43_44.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24240,⟨sg24232,⟨sg24228,⟨sg24226,⟨sg24225,True.intro,True.intro⟩,⟨sg24227,True.intro,True.intro⟩⟩,⟨sg24230,⟨sg24229,True.intro,True.intro⟩,⟨sg24231,True.intro,True.intro⟩⟩⟩,⟨sg24236,⟨sg24234,⟨sg24233,True.intro,True.intro⟩,⟨sg24235,True.intro,True.intro⟩⟩,⟨sg24238,⟨sg24237,True.intro,True.intro⟩,⟨sg24239,True.intro,True.intro⟩⟩⟩⟩,⟨sg24248,⟨sg24244,⟨sg24242,⟨sg24241,True.intro,True.intro⟩,⟨sg24243,True.intro,True.intro⟩⟩,⟨sg24246,⟨sg24245,True.intro,True.intro⟩,⟨sg24247,True.intro,True.intro⟩⟩⟩,⟨sg24252,⟨sg24250,⟨sg24249,True.intro,True.intro⟩,⟨sg24251,True.intro,True.intro⟩⟩,⟨sg24254,⟨sg24253,True.intro,True.intro⟩,⟨sg24255,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_45All : degreeTree43_45.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24224,degreeTree43_43All,degreeTree43_44All⟩

lemma degreeTree43_46All : degreeTree43_46.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24272,⟨sg24264,⟨sg24260,⟨sg24258,⟨sg24257,True.intro,True.intro⟩,⟨sg24259,True.intro,True.intro⟩⟩,⟨sg24262,⟨sg24261,True.intro,True.intro⟩,⟨sg24263,True.intro,True.intro⟩⟩⟩,⟨sg24268,⟨sg24266,⟨sg24265,True.intro,True.intro⟩,⟨sg24267,True.intro,True.intro⟩⟩,⟨sg24270,⟨sg24269,True.intro,True.intro⟩,⟨sg24271,True.intro,True.intro⟩⟩⟩⟩,⟨sg24280,⟨sg24276,⟨sg24274,⟨sg24273,True.intro,True.intro⟩,⟨sg24275,True.intro,True.intro⟩⟩,⟨sg24278,⟨sg24277,True.intro,True.intro⟩,⟨sg24279,True.intro,True.intro⟩⟩⟩,⟨sg24284,⟨sg24282,⟨sg24281,True.intro,True.intro⟩,⟨sg24283,True.intro,True.intro⟩⟩,⟨sg24286,⟨sg24285,True.intro,True.intro⟩,⟨sg24287,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_47All : degreeTree43_47.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24304,⟨sg24296,⟨sg24292,⟨sg24290,⟨sg24289,True.intro,True.intro⟩,⟨sg24291,True.intro,True.intro⟩⟩,⟨sg24294,⟨sg24293,True.intro,True.intro⟩,⟨sg24295,True.intro,True.intro⟩⟩⟩,⟨sg24300,⟨sg24298,⟨sg24297,True.intro,True.intro⟩,⟨sg24299,True.intro,True.intro⟩⟩,⟨sg24302,⟨sg24301,True.intro,True.intro⟩,⟨sg24303,True.intro,True.intro⟩⟩⟩⟩,⟨sg24312,⟨sg24308,⟨sg24306,⟨sg24305,True.intro,True.intro⟩,⟨sg24307,True.intro,True.intro⟩⟩,⟨sg24310,⟨sg24309,True.intro,True.intro⟩,⟨sg24311,True.intro,True.intro⟩⟩⟩,⟨sg24316,⟨sg24314,⟨sg24313,True.intro,True.intro⟩,⟨sg24315,True.intro,True.intro⟩⟩,⟨sg24318,⟨sg24317,True.intro,True.intro⟩,⟨sg24319,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_48All : degreeTree43_48.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24288,degreeTree43_46All,degreeTree43_47All⟩

lemma degreeTree43_49All : degreeTree43_49.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24256,degreeTree43_45All,degreeTree43_48All⟩

lemma degreeTree43_50All : degreeTree43_50.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24329,⟨sg24325,⟨sg24323,⟨sg24322,⟨sg24321,True.intro,True.intro⟩,True.intro⟩,⟨sg24324,True.intro,True.intro⟩⟩,⟨sg24327,⟨sg24326,True.intro,True.intro⟩,⟨sg24328,True.intro,True.intro⟩⟩⟩,⟨sg24333,⟨sg24331,⟨sg24330,True.intro,True.intro⟩,⟨sg24332,True.intro,True.intro⟩⟩,⟨sg24335,⟨sg24334,True.intro,True.intro⟩,⟨sg24336,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_51All : degreeTree43_51.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24345,⟨sg24341,⟨sg24339,⟨sg24338,True.intro,True.intro⟩,⟨sg24340,True.intro,True.intro⟩⟩,⟨sg24343,⟨sg24342,True.intro,True.intro⟩,⟨sg24344,True.intro,True.intro⟩⟩⟩,⟨sg24349,⟨sg24347,⟨sg24346,True.intro,True.intro⟩,⟨sg24348,True.intro,True.intro⟩⟩,⟨sg24351,⟨sg24350,True.intro,True.intro⟩,⟨sg24352,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_52All : degreeTree43_52.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24337,degreeTree43_50All,degreeTree43_51All⟩

lemma degreeTree43_53All : degreeTree43_53.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24369,⟨sg24361,⟨sg24357,⟨sg24355,⟨sg24354,True.intro,True.intro⟩,⟨sg24356,True.intro,True.intro⟩⟩,⟨sg24359,⟨sg24358,True.intro,True.intro⟩,⟨sg24360,True.intro,True.intro⟩⟩⟩,⟨sg24365,⟨sg24363,⟨sg24362,True.intro,True.intro⟩,⟨sg24364,True.intro,True.intro⟩⟩,⟨sg24367,⟨sg24366,True.intro,True.intro⟩,⟨sg24368,True.intro,True.intro⟩⟩⟩⟩,⟨sg24377,⟨sg24373,⟨sg24371,⟨sg24370,True.intro,True.intro⟩,⟨sg24372,True.intro,True.intro⟩⟩,⟨sg24375,⟨sg24374,True.intro,True.intro⟩,⟨sg24376,True.intro,True.intro⟩⟩⟩,⟨sg24381,⟨sg24379,⟨sg24378,True.intro,True.intro⟩,⟨sg24380,True.intro,True.intro⟩⟩,⟨sg24383,⟨sg24382,True.intro,True.intro⟩,⟨sg24384,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_54All : degreeTree43_54.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24353,degreeTree43_52All,degreeTree43_53All⟩

lemma degreeTree43_55All : degreeTree43_55.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24401,⟨sg24393,⟨sg24389,⟨sg24387,⟨sg24386,True.intro,True.intro⟩,⟨sg24388,True.intro,True.intro⟩⟩,⟨sg24391,⟨sg24390,True.intro,True.intro⟩,⟨sg24392,True.intro,True.intro⟩⟩⟩,⟨sg24397,⟨sg24395,⟨sg24394,True.intro,True.intro⟩,⟨sg24396,True.intro,True.intro⟩⟩,⟨sg24399,⟨sg24398,True.intro,True.intro⟩,⟨sg24400,True.intro,True.intro⟩⟩⟩⟩,⟨sg24409,⟨sg24405,⟨sg24403,⟨sg24402,True.intro,True.intro⟩,⟨sg24404,True.intro,True.intro⟩⟩,⟨sg24407,⟨sg24406,True.intro,True.intro⟩,⟨sg24408,True.intro,True.intro⟩⟩⟩,⟨sg24413,⟨sg24411,⟨sg24410,True.intro,True.intro⟩,⟨sg24412,True.intro,True.intro⟩⟩,⟨sg24415,⟨sg24414,True.intro,True.intro⟩,⟨sg24416,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_56All : degreeTree43_56.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24433,⟨sg24425,⟨sg24421,⟨sg24419,⟨sg24418,True.intro,True.intro⟩,⟨sg24420,True.intro,True.intro⟩⟩,⟨sg24423,⟨sg24422,True.intro,True.intro⟩,⟨sg24424,True.intro,True.intro⟩⟩⟩,⟨sg24429,⟨sg24427,⟨sg24426,True.intro,True.intro⟩,⟨sg24428,True.intro,True.intro⟩⟩,⟨sg24431,⟨sg24430,True.intro,True.intro⟩,⟨sg24432,True.intro,True.intro⟩⟩⟩⟩,⟨sg24441,⟨sg24437,⟨sg24435,⟨sg24434,True.intro,True.intro⟩,⟨sg24436,True.intro,True.intro⟩⟩,⟨sg24439,⟨sg24438,True.intro,True.intro⟩,⟨sg24440,True.intro,True.intro⟩⟩⟩,⟨sg24445,⟨sg24443,⟨sg24442,True.intro,True.intro⟩,⟨sg24444,True.intro,True.intro⟩⟩,⟨sg24447,⟨sg24446,True.intro,True.intro⟩,⟨sg24448,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_57All : degreeTree43_57.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24417,degreeTree43_55All,degreeTree43_56All⟩

lemma degreeTree43_58All : degreeTree43_58.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24385,degreeTree43_54All,degreeTree43_57All⟩

lemma degreeTree43_59All : degreeTree43_59.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24320,degreeTree43_49All,degreeTree43_58All⟩

lemma degreeTree43_60All : degreeTree43_60.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24458,⟨sg24454,⟨sg24452,⟨sg24451,⟨sg24450,True.intro,True.intro⟩,True.intro⟩,⟨sg24453,True.intro,True.intro⟩⟩,⟨sg24456,⟨sg24455,True.intro,True.intro⟩,⟨sg24457,True.intro,True.intro⟩⟩⟩,⟨sg24462,⟨sg24460,⟨sg24459,True.intro,True.intro⟩,⟨sg24461,True.intro,True.intro⟩⟩,⟨sg24464,⟨sg24463,True.intro,True.intro⟩,⟨sg24465,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_61All : degreeTree43_61.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24474,⟨sg24470,⟨sg24468,⟨sg24467,True.intro,True.intro⟩,⟨sg24469,True.intro,True.intro⟩⟩,⟨sg24472,⟨sg24471,True.intro,True.intro⟩,⟨sg24473,True.intro,True.intro⟩⟩⟩,⟨sg24478,⟨sg24476,⟨sg24475,True.intro,True.intro⟩,⟨sg24477,True.intro,True.intro⟩⟩,⟨sg24480,⟨sg24479,True.intro,True.intro⟩,⟨sg24481,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_62All : degreeTree43_62.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24466,degreeTree43_60All,degreeTree43_61All⟩

lemma degreeTree43_63All : degreeTree43_63.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24498,⟨sg24490,⟨sg24486,⟨sg24484,⟨sg24483,True.intro,True.intro⟩,⟨sg24485,True.intro,True.intro⟩⟩,⟨sg24488,⟨sg24487,True.intro,True.intro⟩,⟨sg24489,True.intro,True.intro⟩⟩⟩,⟨sg24494,⟨sg24492,⟨sg24491,True.intro,True.intro⟩,⟨sg24493,True.intro,True.intro⟩⟩,⟨sg24496,⟨sg24495,True.intro,True.intro⟩,⟨sg24497,True.intro,True.intro⟩⟩⟩⟩,⟨sg24506,⟨sg24502,⟨sg24500,⟨sg24499,True.intro,True.intro⟩,⟨sg24501,True.intro,True.intro⟩⟩,⟨sg24504,⟨sg24503,True.intro,True.intro⟩,⟨sg24505,True.intro,True.intro⟩⟩⟩,⟨sg24510,⟨sg24508,⟨sg24507,True.intro,True.intro⟩,⟨sg24509,True.intro,True.intro⟩⟩,⟨sg24512,⟨sg24511,True.intro,True.intro⟩,⟨sg24513,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_64All : degreeTree43_64.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24482,degreeTree43_62All,degreeTree43_63All⟩

lemma degreeTree43_65All : degreeTree43_65.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24530,⟨sg24522,⟨sg24518,⟨sg24516,⟨sg24515,True.intro,True.intro⟩,⟨sg24517,True.intro,True.intro⟩⟩,⟨sg24520,⟨sg24519,True.intro,True.intro⟩,⟨sg24521,True.intro,True.intro⟩⟩⟩,⟨sg24526,⟨sg24524,⟨sg24523,True.intro,True.intro⟩,⟨sg24525,True.intro,True.intro⟩⟩,⟨sg24528,⟨sg24527,True.intro,True.intro⟩,⟨sg24529,True.intro,True.intro⟩⟩⟩⟩,⟨sg24538,⟨sg24534,⟨sg24532,⟨sg24531,True.intro,True.intro⟩,⟨sg24533,True.intro,True.intro⟩⟩,⟨sg24536,⟨sg24535,True.intro,True.intro⟩,⟨sg24537,True.intro,True.intro⟩⟩⟩,⟨sg24542,⟨sg24540,⟨sg24539,True.intro,True.intro⟩,⟨sg24541,True.intro,True.intro⟩⟩,⟨sg24544,⟨sg24543,True.intro,True.intro⟩,⟨sg24545,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_66All : degreeTree43_66.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24562,⟨sg24554,⟨sg24550,⟨sg24548,⟨sg24547,True.intro,True.intro⟩,⟨sg24549,True.intro,True.intro⟩⟩,⟨sg24552,⟨sg24551,True.intro,True.intro⟩,⟨sg24553,True.intro,True.intro⟩⟩⟩,⟨sg24558,⟨sg24556,⟨sg24555,True.intro,True.intro⟩,⟨sg24557,True.intro,True.intro⟩⟩,⟨sg24560,⟨sg24559,True.intro,True.intro⟩,⟨sg24561,True.intro,True.intro⟩⟩⟩⟩,⟨sg24570,⟨sg24566,⟨sg24564,⟨sg24563,True.intro,True.intro⟩,⟨sg24565,True.intro,True.intro⟩⟩,⟨sg24568,⟨sg24567,True.intro,True.intro⟩,⟨sg24569,True.intro,True.intro⟩⟩⟩,⟨sg24574,⟨sg24572,⟨sg24571,True.intro,True.intro⟩,⟨sg24573,True.intro,True.intro⟩⟩,⟨sg24576,⟨sg24575,True.intro,True.intro⟩,⟨sg24577,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_67All : degreeTree43_67.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24546,degreeTree43_65All,degreeTree43_66All⟩

lemma degreeTree43_68All : degreeTree43_68.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24514,degreeTree43_64All,degreeTree43_67All⟩

lemma degreeTree43_69All : degreeTree43_69.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24587,⟨sg24583,⟨sg24581,⟨sg24580,⟨sg24579,True.intro,True.intro⟩,True.intro⟩,⟨sg24582,True.intro,True.intro⟩⟩,⟨sg24585,⟨sg24584,True.intro,True.intro⟩,⟨sg24586,True.intro,True.intro⟩⟩⟩,⟨sg24591,⟨sg24589,⟨sg24588,True.intro,True.intro⟩,⟨sg24590,True.intro,True.intro⟩⟩,⟨sg24593,⟨sg24592,True.intro,True.intro⟩,⟨sg24594,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_70All : degreeTree43_70.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24603,⟨sg24599,⟨sg24597,⟨sg24596,True.intro,True.intro⟩,⟨sg24598,True.intro,True.intro⟩⟩,⟨sg24601,⟨sg24600,True.intro,True.intro⟩,⟨sg24602,True.intro,True.intro⟩⟩⟩,⟨sg24607,⟨sg24605,⟨sg24604,True.intro,True.intro⟩,⟨sg24606,True.intro,True.intro⟩⟩,⟨sg24609,⟨sg24608,True.intro,True.intro⟩,⟨sg24610,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_71All : degreeTree43_71.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24595,degreeTree43_69All,degreeTree43_70All⟩

lemma degreeTree43_72All : degreeTree43_72.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24627,⟨sg24619,⟨sg24615,⟨sg24613,⟨sg24612,True.intro,True.intro⟩,⟨sg24614,True.intro,True.intro⟩⟩,⟨sg24617,⟨sg24616,True.intro,True.intro⟩,⟨sg24618,True.intro,True.intro⟩⟩⟩,⟨sg24623,⟨sg24621,⟨sg24620,True.intro,True.intro⟩,⟨sg24622,True.intro,True.intro⟩⟩,⟨sg24625,⟨sg24624,True.intro,True.intro⟩,⟨sg24626,True.intro,True.intro⟩⟩⟩⟩,⟨sg24635,⟨sg24631,⟨sg24629,⟨sg24628,True.intro,True.intro⟩,⟨sg24630,True.intro,True.intro⟩⟩,⟨sg24633,⟨sg24632,True.intro,True.intro⟩,⟨sg24634,True.intro,True.intro⟩⟩⟩,⟨sg24639,⟨sg24637,⟨sg24636,True.intro,True.intro⟩,⟨sg24638,True.intro,True.intro⟩⟩,⟨sg24641,⟨sg24640,True.intro,True.intro⟩,⟨sg24642,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_73All : degreeTree43_73.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24611,degreeTree43_71All,degreeTree43_72All⟩

lemma degreeTree43_74All : degreeTree43_74.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24659,⟨sg24651,⟨sg24647,⟨sg24645,⟨sg24644,True.intro,True.intro⟩,⟨sg24646,True.intro,True.intro⟩⟩,⟨sg24649,⟨sg24648,True.intro,True.intro⟩,⟨sg24650,True.intro,True.intro⟩⟩⟩,⟨sg24655,⟨sg24653,⟨sg24652,True.intro,True.intro⟩,⟨sg24654,True.intro,True.intro⟩⟩,⟨sg24657,⟨sg24656,True.intro,True.intro⟩,⟨sg24658,True.intro,True.intro⟩⟩⟩⟩,⟨sg24667,⟨sg24663,⟨sg24661,⟨sg24660,True.intro,True.intro⟩,⟨sg24662,True.intro,True.intro⟩⟩,⟨sg24665,⟨sg24664,True.intro,True.intro⟩,⟨sg24666,True.intro,True.intro⟩⟩⟩,⟨sg24671,⟨sg24669,⟨sg24668,True.intro,True.intro⟩,⟨sg24670,True.intro,True.intro⟩⟩,⟨sg24673,⟨sg24672,True.intro,True.intro⟩,⟨sg24674,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_75All : degreeTree43_75.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24691,⟨sg24683,⟨sg24679,⟨sg24677,⟨sg24676,True.intro,True.intro⟩,⟨sg24678,True.intro,True.intro⟩⟩,⟨sg24681,⟨sg24680,True.intro,True.intro⟩,⟨sg24682,True.intro,True.intro⟩⟩⟩,⟨sg24687,⟨sg24685,⟨sg24684,True.intro,True.intro⟩,⟨sg24686,True.intro,True.intro⟩⟩,⟨sg24689,⟨sg24688,True.intro,True.intro⟩,⟨sg24690,True.intro,True.intro⟩⟩⟩⟩,⟨sg24699,⟨sg24695,⟨sg24693,⟨sg24692,True.intro,True.intro⟩,⟨sg24694,True.intro,True.intro⟩⟩,⟨sg24697,⟨sg24696,True.intro,True.intro⟩,⟨sg24698,True.intro,True.intro⟩⟩⟩,⟨sg24703,⟨sg24701,⟨sg24700,True.intro,True.intro⟩,⟨sg24702,True.intro,True.intro⟩⟩,⟨sg24705,⟨sg24704,True.intro,True.intro⟩,⟨sg24706,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_76All : degreeTree43_76.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24675,degreeTree43_74All,degreeTree43_75All⟩

lemma degreeTree43_77All : degreeTree43_77.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24643,degreeTree43_73All,degreeTree43_76All⟩

lemma degreeTree43_78All : degreeTree43_78.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24578,degreeTree43_68All,degreeTree43_77All⟩

lemma degreeTree43_79All : degreeTree43_79.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24449,degreeTree43_59All,degreeTree43_78All⟩

lemma degreeTree43_80All : degreeTree43_80.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24191,degreeTree43_40All,degreeTree43_79All⟩

lemma degreeTree43_81All : degreeTree43_81.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24716,⟨sg24712,⟨sg24710,⟨sg24709,⟨sg24708,True.intro,True.intro⟩,True.intro⟩,⟨sg24711,True.intro,True.intro⟩⟩,⟨sg24714,⟨sg24713,True.intro,True.intro⟩,⟨sg24715,True.intro,True.intro⟩⟩⟩,⟨sg24720,⟨sg24718,⟨sg24717,True.intro,True.intro⟩,⟨sg24719,True.intro,True.intro⟩⟩,⟨sg24722,⟨sg24721,True.intro,True.intro⟩,⟨sg24723,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_82All : degreeTree43_82.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24732,⟨sg24728,⟨sg24726,⟨sg24725,True.intro,True.intro⟩,⟨sg24727,True.intro,True.intro⟩⟩,⟨sg24730,⟨sg24729,True.intro,True.intro⟩,⟨sg24731,True.intro,True.intro⟩⟩⟩,⟨sg24736,⟨sg24734,⟨sg24733,True.intro,True.intro⟩,⟨sg24735,True.intro,True.intro⟩⟩,⟨sg24738,⟨sg24737,True.intro,True.intro⟩,⟨sg24739,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_83All : degreeTree43_83.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24724,degreeTree43_81All,degreeTree43_82All⟩

lemma degreeTree43_84All : degreeTree43_84.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24756,⟨sg24748,⟨sg24744,⟨sg24742,⟨sg24741,True.intro,True.intro⟩,⟨sg24743,True.intro,True.intro⟩⟩,⟨sg24746,⟨sg24745,True.intro,True.intro⟩,⟨sg24747,True.intro,True.intro⟩⟩⟩,⟨sg24752,⟨sg24750,⟨sg24749,True.intro,True.intro⟩,⟨sg24751,True.intro,True.intro⟩⟩,⟨sg24754,⟨sg24753,True.intro,True.intro⟩,⟨sg24755,True.intro,True.intro⟩⟩⟩⟩,⟨sg24764,⟨sg24760,⟨sg24758,⟨sg24757,True.intro,True.intro⟩,⟨sg24759,True.intro,True.intro⟩⟩,⟨sg24762,⟨sg24761,True.intro,True.intro⟩,⟨sg24763,True.intro,True.intro⟩⟩⟩,⟨sg24768,⟨sg24766,⟨sg24765,True.intro,True.intro⟩,⟨sg24767,True.intro,True.intro⟩⟩,⟨sg24770,⟨sg24769,True.intro,True.intro⟩,⟨sg24771,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_85All : degreeTree43_85.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24740,degreeTree43_83All,degreeTree43_84All⟩

lemma degreeTree43_86All : degreeTree43_86.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24781,⟨sg24777,⟨sg24775,⟨sg24774,⟨sg24773,True.intro,True.intro⟩,True.intro⟩,⟨sg24776,True.intro,True.intro⟩⟩,⟨sg24779,⟨sg24778,True.intro,True.intro⟩,⟨sg24780,True.intro,True.intro⟩⟩⟩,⟨sg24785,⟨sg24783,⟨sg24782,True.intro,True.intro⟩,⟨sg24784,True.intro,True.intro⟩⟩,⟨sg24787,⟨sg24786,True.intro,True.intro⟩,⟨sg24788,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_87All : degreeTree43_87.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24797,⟨sg24793,⟨sg24791,⟨sg24790,True.intro,True.intro⟩,⟨sg24792,True.intro,True.intro⟩⟩,⟨sg24795,⟨sg24794,True.intro,True.intro⟩,⟨sg24796,True.intro,True.intro⟩⟩⟩,⟨sg24801,⟨sg24799,⟨sg24798,True.intro,True.intro⟩,⟨sg24800,True.intro,True.intro⟩⟩,⟨sg24803,⟨sg24802,True.intro,True.intro⟩,⟨sg24804,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_88All : degreeTree43_88.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24789,degreeTree43_86All,degreeTree43_87All⟩

lemma degreeTree43_89All : degreeTree43_89.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24821,⟨sg24813,⟨sg24809,⟨sg24807,⟨sg24806,True.intro,True.intro⟩,⟨sg24808,True.intro,True.intro⟩⟩,⟨sg24811,⟨sg24810,True.intro,True.intro⟩,⟨sg24812,True.intro,True.intro⟩⟩⟩,⟨sg24817,⟨sg24815,⟨sg24814,True.intro,True.intro⟩,⟨sg24816,True.intro,True.intro⟩⟩,⟨sg24819,⟨sg24818,True.intro,True.intro⟩,⟨sg24820,True.intro,True.intro⟩⟩⟩⟩,⟨sg24829,⟨sg24825,⟨sg24823,⟨sg24822,True.intro,True.intro⟩,⟨sg24824,True.intro,True.intro⟩⟩,⟨sg24827,⟨sg24826,True.intro,True.intro⟩,⟨sg24828,True.intro,True.intro⟩⟩⟩,⟨sg24833,⟨sg24831,⟨sg24830,True.intro,True.intro⟩,⟨sg24832,True.intro,True.intro⟩⟩,⟨sg24835,⟨sg24834,True.intro,True.intro⟩,⟨sg24836,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_90All : degreeTree43_90.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24805,degreeTree43_88All,degreeTree43_89All⟩

lemma degreeTree43_91All : degreeTree43_91.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24772,degreeTree43_85All,degreeTree43_90All⟩

lemma degreeTree43_92All : degreeTree43_92.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24846,⟨sg24842,⟨sg24840,⟨sg24839,⟨sg24838,True.intro,True.intro⟩,True.intro⟩,⟨sg24841,True.intro,True.intro⟩⟩,⟨sg24844,⟨sg24843,True.intro,True.intro⟩,⟨sg24845,True.intro,True.intro⟩⟩⟩,⟨sg24850,⟨sg24848,⟨sg24847,True.intro,True.intro⟩,⟨sg24849,True.intro,True.intro⟩⟩,⟨sg24852,⟨sg24851,True.intro,True.intro⟩,⟨sg24853,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_93All : degreeTree43_93.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24862,⟨sg24858,⟨sg24856,⟨sg24855,True.intro,True.intro⟩,⟨sg24857,True.intro,True.intro⟩⟩,⟨sg24860,⟨sg24859,True.intro,True.intro⟩,⟨sg24861,True.intro,True.intro⟩⟩⟩,⟨sg24866,⟨sg24864,⟨sg24863,True.intro,True.intro⟩,⟨sg24865,True.intro,True.intro⟩⟩,⟨sg24868,⟨sg24867,True.intro,True.intro⟩,⟨sg24869,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_94All : degreeTree43_94.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24854,degreeTree43_92All,degreeTree43_93All⟩

lemma degreeTree43_95All : degreeTree43_95.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24886,⟨sg24878,⟨sg24874,⟨sg24872,⟨sg24871,True.intro,True.intro⟩,⟨sg24873,True.intro,True.intro⟩⟩,⟨sg24876,⟨sg24875,True.intro,True.intro⟩,⟨sg24877,True.intro,True.intro⟩⟩⟩,⟨sg24882,⟨sg24880,⟨sg24879,True.intro,True.intro⟩,⟨sg24881,True.intro,True.intro⟩⟩,⟨sg24884,⟨sg24883,True.intro,True.intro⟩,⟨sg24885,True.intro,True.intro⟩⟩⟩⟩,⟨sg24894,⟨sg24890,⟨sg24888,⟨sg24887,True.intro,True.intro⟩,⟨sg24889,True.intro,True.intro⟩⟩,⟨sg24892,⟨sg24891,True.intro,True.intro⟩,⟨sg24893,True.intro,True.intro⟩⟩⟩,⟨sg24898,⟨sg24896,⟨sg24895,True.intro,True.intro⟩,⟨sg24897,True.intro,True.intro⟩⟩,⟨sg24900,⟨sg24899,True.intro,True.intro⟩,⟨sg24901,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_96All : degreeTree43_96.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24870,degreeTree43_94All,degreeTree43_95All⟩

lemma degreeTree43_97All : degreeTree43_97.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24918,⟨sg24910,⟨sg24906,⟨sg24904,⟨sg24903,True.intro,True.intro⟩,⟨sg24905,True.intro,True.intro⟩⟩,⟨sg24908,⟨sg24907,True.intro,True.intro⟩,⟨sg24909,True.intro,True.intro⟩⟩⟩,⟨sg24914,⟨sg24912,⟨sg24911,True.intro,True.intro⟩,⟨sg24913,True.intro,True.intro⟩⟩,⟨sg24916,⟨sg24915,True.intro,True.intro⟩,⟨sg24917,True.intro,True.intro⟩⟩⟩⟩,⟨sg24926,⟨sg24922,⟨sg24920,⟨sg24919,True.intro,True.intro⟩,⟨sg24921,True.intro,True.intro⟩⟩,⟨sg24924,⟨sg24923,True.intro,True.intro⟩,⟨sg24925,True.intro,True.intro⟩⟩⟩,⟨sg24930,⟨sg24928,⟨sg24927,True.intro,True.intro⟩,⟨sg24929,True.intro,True.intro⟩⟩,⟨sg24932,⟨sg24931,True.intro,True.intro⟩,⟨sg24933,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_98All : degreeTree43_98.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24950,⟨sg24942,⟨sg24938,⟨sg24936,⟨sg24935,True.intro,True.intro⟩,⟨sg24937,True.intro,True.intro⟩⟩,⟨sg24940,⟨sg24939,True.intro,True.intro⟩,⟨sg24941,True.intro,True.intro⟩⟩⟩,⟨sg24946,⟨sg24944,⟨sg24943,True.intro,True.intro⟩,⟨sg24945,True.intro,True.intro⟩⟩,⟨sg24948,⟨sg24947,True.intro,True.intro⟩,⟨sg24949,True.intro,True.intro⟩⟩⟩⟩,⟨sg24958,⟨sg24954,⟨sg24952,⟨sg24951,True.intro,True.intro⟩,⟨sg24953,True.intro,True.intro⟩⟩,⟨sg24956,⟨sg24955,True.intro,True.intro⟩,⟨sg24957,True.intro,True.intro⟩⟩⟩,⟨sg24962,⟨sg24960,⟨sg24959,True.intro,True.intro⟩,⟨sg24961,True.intro,True.intro⟩⟩,⟨sg24964,⟨sg24963,True.intro,True.intro⟩,⟨sg24965,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_99All : degreeTree43_99.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24934,degreeTree43_97All,degreeTree43_98All⟩

lemma degreeTree43_100All : degreeTree43_100.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24902,degreeTree43_96All,degreeTree43_99All⟩

lemma degreeTree43_101All : degreeTree43_101.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24837,degreeTree43_91All,degreeTree43_100All⟩

lemma degreeTree43_102All : degreeTree43_102.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24975,⟨sg24971,⟨sg24969,⟨sg24968,⟨sg24967,True.intro,True.intro⟩,True.intro⟩,⟨sg24970,True.intro,True.intro⟩⟩,⟨sg24973,⟨sg24972,True.intro,True.intro⟩,⟨sg24974,True.intro,True.intro⟩⟩⟩,⟨sg24979,⟨sg24977,⟨sg24976,True.intro,True.intro⟩,⟨sg24978,True.intro,True.intro⟩⟩,⟨sg24981,⟨sg24980,True.intro,True.intro⟩,⟨sg24982,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_103All : degreeTree43_103.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24991,⟨sg24987,⟨sg24985,⟨sg24984,True.intro,True.intro⟩,⟨sg24986,True.intro,True.intro⟩⟩,⟨sg24989,⟨sg24988,True.intro,True.intro⟩,⟨sg24990,True.intro,True.intro⟩⟩⟩,⟨sg24995,⟨sg24993,⟨sg24992,True.intro,True.intro⟩,⟨sg24994,True.intro,True.intro⟩⟩,⟨sg24997,⟨sg24996,True.intro,True.intro⟩,⟨sg24998,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_104All : degreeTree43_104.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24983,degreeTree43_102All,degreeTree43_103All⟩

lemma degreeTree43_105All : degreeTree43_105.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25015,⟨sg25007,⟨sg25003,⟨sg25001,⟨sg25000,True.intro,True.intro⟩,⟨sg25002,True.intro,True.intro⟩⟩,⟨sg25005,⟨sg25004,True.intro,True.intro⟩,⟨sg25006,True.intro,True.intro⟩⟩⟩,⟨sg25011,⟨sg25009,⟨sg25008,True.intro,True.intro⟩,⟨sg25010,True.intro,True.intro⟩⟩,⟨sg25013,⟨sg25012,True.intro,True.intro⟩,⟨sg25014,True.intro,True.intro⟩⟩⟩⟩,⟨sg25023,⟨sg25019,⟨sg25017,⟨sg25016,True.intro,True.intro⟩,⟨sg25018,True.intro,True.intro⟩⟩,⟨sg25021,⟨sg25020,True.intro,True.intro⟩,⟨sg25022,True.intro,True.intro⟩⟩⟩,⟨sg25027,⟨sg25025,⟨sg25024,True.intro,True.intro⟩,⟨sg25026,True.intro,True.intro⟩⟩,⟨sg25029,⟨sg25028,True.intro,True.intro⟩,⟨sg25030,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_106All : degreeTree43_106.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24999,degreeTree43_104All,degreeTree43_105All⟩

lemma degreeTree43_107All : degreeTree43_107.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25047,⟨sg25039,⟨sg25035,⟨sg25033,⟨sg25032,True.intro,True.intro⟩,⟨sg25034,True.intro,True.intro⟩⟩,⟨sg25037,⟨sg25036,True.intro,True.intro⟩,⟨sg25038,True.intro,True.intro⟩⟩⟩,⟨sg25043,⟨sg25041,⟨sg25040,True.intro,True.intro⟩,⟨sg25042,True.intro,True.intro⟩⟩,⟨sg25045,⟨sg25044,True.intro,True.intro⟩,⟨sg25046,True.intro,True.intro⟩⟩⟩⟩,⟨sg25055,⟨sg25051,⟨sg25049,⟨sg25048,True.intro,True.intro⟩,⟨sg25050,True.intro,True.intro⟩⟩,⟨sg25053,⟨sg25052,True.intro,True.intro⟩,⟨sg25054,True.intro,True.intro⟩⟩⟩,⟨sg25059,⟨sg25057,⟨sg25056,True.intro,True.intro⟩,⟨sg25058,True.intro,True.intro⟩⟩,⟨sg25061,⟨sg25060,True.intro,True.intro⟩,⟨sg25062,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_108All : degreeTree43_108.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25079,⟨sg25071,⟨sg25067,⟨sg25065,⟨sg25064,True.intro,True.intro⟩,⟨sg25066,True.intro,True.intro⟩⟩,⟨sg25069,⟨sg25068,True.intro,True.intro⟩,⟨sg25070,True.intro,True.intro⟩⟩⟩,⟨sg25075,⟨sg25073,⟨sg25072,True.intro,True.intro⟩,⟨sg25074,True.intro,True.intro⟩⟩,⟨sg25077,⟨sg25076,True.intro,True.intro⟩,⟨sg25078,True.intro,True.intro⟩⟩⟩⟩,⟨sg25087,⟨sg25083,⟨sg25081,⟨sg25080,True.intro,True.intro⟩,⟨sg25082,True.intro,True.intro⟩⟩,⟨sg25085,⟨sg25084,True.intro,True.intro⟩,⟨sg25086,True.intro,True.intro⟩⟩⟩,⟨sg25091,⟨sg25089,⟨sg25088,True.intro,True.intro⟩,⟨sg25090,True.intro,True.intro⟩⟩,⟨sg25093,⟨sg25092,True.intro,True.intro⟩,⟨sg25094,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_109All : degreeTree43_109.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25063,degreeTree43_107All,degreeTree43_108All⟩

lemma degreeTree43_110All : degreeTree43_110.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25031,degreeTree43_106All,degreeTree43_109All⟩

lemma degreeTree43_111All : degreeTree43_111.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25104,⟨sg25100,⟨sg25098,⟨sg25097,⟨sg25096,True.intro,True.intro⟩,True.intro⟩,⟨sg25099,True.intro,True.intro⟩⟩,⟨sg25102,⟨sg25101,True.intro,True.intro⟩,⟨sg25103,True.intro,True.intro⟩⟩⟩,⟨sg25108,⟨sg25106,⟨sg25105,True.intro,True.intro⟩,⟨sg25107,True.intro,True.intro⟩⟩,⟨sg25110,⟨sg25109,True.intro,True.intro⟩,⟨sg25111,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_112All : degreeTree43_112.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25120,⟨sg25116,⟨sg25114,⟨sg25113,True.intro,True.intro⟩,⟨sg25115,True.intro,True.intro⟩⟩,⟨sg25118,⟨sg25117,True.intro,True.intro⟩,⟨sg25119,True.intro,True.intro⟩⟩⟩,⟨sg25124,⟨sg25122,⟨sg25121,True.intro,True.intro⟩,⟨sg25123,True.intro,True.intro⟩⟩,⟨sg25126,⟨sg25125,True.intro,True.intro⟩,⟨sg25127,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_113All : degreeTree43_113.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25112,degreeTree43_111All,degreeTree43_112All⟩

lemma degreeTree43_114All : degreeTree43_114.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25144,⟨sg25136,⟨sg25132,⟨sg25130,⟨sg25129,True.intro,True.intro⟩,⟨sg25131,True.intro,True.intro⟩⟩,⟨sg25134,⟨sg25133,True.intro,True.intro⟩,⟨sg25135,True.intro,True.intro⟩⟩⟩,⟨sg25140,⟨sg25138,⟨sg25137,True.intro,True.intro⟩,⟨sg25139,True.intro,True.intro⟩⟩,⟨sg25142,⟨sg25141,True.intro,True.intro⟩,⟨sg25143,True.intro,True.intro⟩⟩⟩⟩,⟨sg25152,⟨sg25148,⟨sg25146,⟨sg25145,True.intro,True.intro⟩,⟨sg25147,True.intro,True.intro⟩⟩,⟨sg25150,⟨sg25149,True.intro,True.intro⟩,⟨sg25151,True.intro,True.intro⟩⟩⟩,⟨sg25156,⟨sg25154,⟨sg25153,True.intro,True.intro⟩,⟨sg25155,True.intro,True.intro⟩⟩,⟨sg25158,⟨sg25157,True.intro,True.intro⟩,⟨sg25159,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_115All : degreeTree43_115.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25128,degreeTree43_113All,degreeTree43_114All⟩

lemma degreeTree43_116All : degreeTree43_116.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25176,⟨sg25168,⟨sg25164,⟨sg25162,⟨sg25161,True.intro,True.intro⟩,⟨sg25163,True.intro,True.intro⟩⟩,⟨sg25166,⟨sg25165,True.intro,True.intro⟩,⟨sg25167,True.intro,True.intro⟩⟩⟩,⟨sg25172,⟨sg25170,⟨sg25169,True.intro,True.intro⟩,⟨sg25171,True.intro,True.intro⟩⟩,⟨sg25174,⟨sg25173,True.intro,True.intro⟩,⟨sg25175,True.intro,True.intro⟩⟩⟩⟩,⟨sg25184,⟨sg25180,⟨sg25178,⟨sg25177,True.intro,True.intro⟩,⟨sg25179,True.intro,True.intro⟩⟩,⟨sg25182,⟨sg25181,True.intro,True.intro⟩,⟨sg25183,True.intro,True.intro⟩⟩⟩,⟨sg25188,⟨sg25186,⟨sg25185,True.intro,True.intro⟩,⟨sg25187,True.intro,True.intro⟩⟩,⟨sg25190,⟨sg25189,True.intro,True.intro⟩,⟨sg25191,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_117All : degreeTree43_117.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25208,⟨sg25200,⟨sg25196,⟨sg25194,⟨sg25193,True.intro,True.intro⟩,⟨sg25195,True.intro,True.intro⟩⟩,⟨sg25198,⟨sg25197,True.intro,True.intro⟩,⟨sg25199,True.intro,True.intro⟩⟩⟩,⟨sg25204,⟨sg25202,⟨sg25201,True.intro,True.intro⟩,⟨sg25203,True.intro,True.intro⟩⟩,⟨sg25206,⟨sg25205,True.intro,True.intro⟩,⟨sg25207,True.intro,True.intro⟩⟩⟩⟩,⟨sg25216,⟨sg25212,⟨sg25210,⟨sg25209,True.intro,True.intro⟩,⟨sg25211,True.intro,True.intro⟩⟩,⟨sg25214,⟨sg25213,True.intro,True.intro⟩,⟨sg25215,True.intro,True.intro⟩⟩⟩,⟨sg25220,⟨sg25218,⟨sg25217,True.intro,True.intro⟩,⟨sg25219,True.intro,True.intro⟩⟩,⟨sg25222,⟨sg25221,True.intro,True.intro⟩,⟨sg25223,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_118All : degreeTree43_118.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25192,degreeTree43_116All,degreeTree43_117All⟩

lemma degreeTree43_119All : degreeTree43_119.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25160,degreeTree43_115All,degreeTree43_118All⟩

lemma degreeTree43_120All : degreeTree43_120.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25095,degreeTree43_110All,degreeTree43_119All⟩

lemma degreeTree43_121All : degreeTree43_121.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24966,degreeTree43_101All,degreeTree43_120All⟩

lemma degreeTree43_122All : degreeTree43_122.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25233,⟨sg25229,⟨sg25227,⟨sg25226,⟨sg25225,True.intro,True.intro⟩,True.intro⟩,⟨sg25228,True.intro,True.intro⟩⟩,⟨sg25231,⟨sg25230,True.intro,True.intro⟩,⟨sg25232,True.intro,True.intro⟩⟩⟩,⟨sg25237,⟨sg25235,⟨sg25234,True.intro,True.intro⟩,⟨sg25236,True.intro,True.intro⟩⟩,⟨sg25239,⟨sg25238,True.intro,True.intro⟩,⟨sg25240,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_123All : degreeTree43_123.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25249,⟨sg25245,⟨sg25243,⟨sg25242,True.intro,True.intro⟩,⟨sg25244,True.intro,True.intro⟩⟩,⟨sg25247,⟨sg25246,True.intro,True.intro⟩,⟨sg25248,True.intro,True.intro⟩⟩⟩,⟨sg25253,⟨sg25251,⟨sg25250,True.intro,True.intro⟩,⟨sg25252,True.intro,True.intro⟩⟩,⟨sg25255,⟨sg25254,True.intro,True.intro⟩,⟨sg25256,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_124All : degreeTree43_124.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25241,degreeTree43_122All,degreeTree43_123All⟩

lemma degreeTree43_125All : degreeTree43_125.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25273,⟨sg25265,⟨sg25261,⟨sg25259,⟨sg25258,True.intro,True.intro⟩,⟨sg25260,True.intro,True.intro⟩⟩,⟨sg25263,⟨sg25262,True.intro,True.intro⟩,⟨sg25264,True.intro,True.intro⟩⟩⟩,⟨sg25269,⟨sg25267,⟨sg25266,True.intro,True.intro⟩,⟨sg25268,True.intro,True.intro⟩⟩,⟨sg25271,⟨sg25270,True.intro,True.intro⟩,⟨sg25272,True.intro,True.intro⟩⟩⟩⟩,⟨sg25281,⟨sg25277,⟨sg25275,⟨sg25274,True.intro,True.intro⟩,⟨sg25276,True.intro,True.intro⟩⟩,⟨sg25279,⟨sg25278,True.intro,True.intro⟩,⟨sg25280,True.intro,True.intro⟩⟩⟩,⟨sg25285,⟨sg25283,⟨sg25282,True.intro,True.intro⟩,⟨sg25284,True.intro,True.intro⟩⟩,⟨sg25287,⟨sg25286,True.intro,True.intro⟩,⟨sg25288,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_126All : degreeTree43_126.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25257,degreeTree43_124All,degreeTree43_125All⟩

lemma degreeTree43_127All : degreeTree43_127.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25305,⟨sg25297,⟨sg25293,⟨sg25291,⟨sg25290,True.intro,True.intro⟩,⟨sg25292,True.intro,True.intro⟩⟩,⟨sg25295,⟨sg25294,True.intro,True.intro⟩,⟨sg25296,True.intro,True.intro⟩⟩⟩,⟨sg25301,⟨sg25299,⟨sg25298,True.intro,True.intro⟩,⟨sg25300,True.intro,True.intro⟩⟩,⟨sg25303,⟨sg25302,True.intro,True.intro⟩,⟨sg25304,True.intro,True.intro⟩⟩⟩⟩,⟨sg25313,⟨sg25309,⟨sg25307,⟨sg25306,True.intro,True.intro⟩,⟨sg25308,True.intro,True.intro⟩⟩,⟨sg25311,⟨sg25310,True.intro,True.intro⟩,⟨sg25312,True.intro,True.intro⟩⟩⟩,⟨sg25317,⟨sg25315,⟨sg25314,True.intro,True.intro⟩,⟨sg25316,True.intro,True.intro⟩⟩,⟨sg25319,⟨sg25318,True.intro,True.intro⟩,⟨sg25320,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_128All : degreeTree43_128.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25337,⟨sg25329,⟨sg25325,⟨sg25323,⟨sg25322,True.intro,True.intro⟩,⟨sg25324,True.intro,True.intro⟩⟩,⟨sg25327,⟨sg25326,True.intro,True.intro⟩,⟨sg25328,True.intro,True.intro⟩⟩⟩,⟨sg25333,⟨sg25331,⟨sg25330,True.intro,True.intro⟩,⟨sg25332,True.intro,True.intro⟩⟩,⟨sg25335,⟨sg25334,True.intro,True.intro⟩,⟨sg25336,True.intro,True.intro⟩⟩⟩⟩,⟨sg25345,⟨sg25341,⟨sg25339,⟨sg25338,True.intro,True.intro⟩,⟨sg25340,True.intro,True.intro⟩⟩,⟨sg25343,⟨sg25342,True.intro,True.intro⟩,⟨sg25344,True.intro,True.intro⟩⟩⟩,⟨sg25349,⟨sg25347,⟨sg25346,True.intro,True.intro⟩,⟨sg25348,True.intro,True.intro⟩⟩,⟨sg25351,⟨sg25350,True.intro,True.intro⟩,⟨sg25352,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_129All : degreeTree43_129.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25321,degreeTree43_127All,degreeTree43_128All⟩

lemma degreeTree43_130All : degreeTree43_130.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25289,degreeTree43_126All,degreeTree43_129All⟩

lemma degreeTree43_131All : degreeTree43_131.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25362,⟨sg25358,⟨sg25356,⟨sg25355,⟨sg25354,True.intro,True.intro⟩,True.intro⟩,⟨sg25357,True.intro,True.intro⟩⟩,⟨sg25360,⟨sg25359,True.intro,True.intro⟩,⟨sg25361,True.intro,True.intro⟩⟩⟩,⟨sg25366,⟨sg25364,⟨sg25363,True.intro,True.intro⟩,⟨sg25365,True.intro,True.intro⟩⟩,⟨sg25368,⟨sg25367,True.intro,True.intro⟩,⟨sg25369,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_132All : degreeTree43_132.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25378,⟨sg25374,⟨sg25372,⟨sg25371,True.intro,True.intro⟩,⟨sg25373,True.intro,True.intro⟩⟩,⟨sg25376,⟨sg25375,True.intro,True.intro⟩,⟨sg25377,True.intro,True.intro⟩⟩⟩,⟨sg25382,⟨sg25380,⟨sg25379,True.intro,True.intro⟩,⟨sg25381,True.intro,True.intro⟩⟩,⟨sg25384,⟨sg25383,True.intro,True.intro⟩,⟨sg25385,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_133All : degreeTree43_133.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25370,degreeTree43_131All,degreeTree43_132All⟩

lemma degreeTree43_134All : degreeTree43_134.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25402,⟨sg25394,⟨sg25390,⟨sg25388,⟨sg25387,True.intro,True.intro⟩,⟨sg25389,True.intro,True.intro⟩⟩,⟨sg25392,⟨sg25391,True.intro,True.intro⟩,⟨sg25393,True.intro,True.intro⟩⟩⟩,⟨sg25398,⟨sg25396,⟨sg25395,True.intro,True.intro⟩,⟨sg25397,True.intro,True.intro⟩⟩,⟨sg25400,⟨sg25399,True.intro,True.intro⟩,⟨sg25401,True.intro,True.intro⟩⟩⟩⟩,⟨sg25410,⟨sg25406,⟨sg25404,⟨sg25403,True.intro,True.intro⟩,⟨sg25405,True.intro,True.intro⟩⟩,⟨sg25408,⟨sg25407,True.intro,True.intro⟩,⟨sg25409,True.intro,True.intro⟩⟩⟩,⟨sg25414,⟨sg25412,⟨sg25411,True.intro,True.intro⟩,⟨sg25413,True.intro,True.intro⟩⟩,⟨sg25416,⟨sg25415,True.intro,True.intro⟩,⟨sg25417,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_135All : degreeTree43_135.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25386,degreeTree43_133All,degreeTree43_134All⟩

lemma degreeTree43_136All : degreeTree43_136.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25434,⟨sg25426,⟨sg25422,⟨sg25420,⟨sg25419,True.intro,True.intro⟩,⟨sg25421,True.intro,True.intro⟩⟩,⟨sg25424,⟨sg25423,True.intro,True.intro⟩,⟨sg25425,True.intro,True.intro⟩⟩⟩,⟨sg25430,⟨sg25428,⟨sg25427,True.intro,True.intro⟩,⟨sg25429,True.intro,True.intro⟩⟩,⟨sg25432,⟨sg25431,True.intro,True.intro⟩,⟨sg25433,True.intro,True.intro⟩⟩⟩⟩,⟨sg25442,⟨sg25438,⟨sg25436,⟨sg25435,True.intro,True.intro⟩,⟨sg25437,True.intro,True.intro⟩⟩,⟨sg25440,⟨sg25439,True.intro,True.intro⟩,⟨sg25441,True.intro,True.intro⟩⟩⟩,⟨sg25446,⟨sg25444,⟨sg25443,True.intro,True.intro⟩,⟨sg25445,True.intro,True.intro⟩⟩,⟨sg25448,⟨sg25447,True.intro,True.intro⟩,⟨sg25449,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_137All : degreeTree43_137.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25466,⟨sg25458,⟨sg25454,⟨sg25452,⟨sg25451,True.intro,True.intro⟩,⟨sg25453,True.intro,True.intro⟩⟩,⟨sg25456,⟨sg25455,True.intro,True.intro⟩,⟨sg25457,True.intro,True.intro⟩⟩⟩,⟨sg25462,⟨sg25460,⟨sg25459,True.intro,True.intro⟩,⟨sg25461,True.intro,True.intro⟩⟩,⟨sg25464,⟨sg25463,True.intro,True.intro⟩,⟨sg25465,True.intro,True.intro⟩⟩⟩⟩,⟨sg25474,⟨sg25470,⟨sg25468,⟨sg25467,True.intro,True.intro⟩,⟨sg25469,True.intro,True.intro⟩⟩,⟨sg25472,⟨sg25471,True.intro,True.intro⟩,⟨sg25473,True.intro,True.intro⟩⟩⟩,⟨sg25478,⟨sg25476,⟨sg25475,True.intro,True.intro⟩,⟨sg25477,True.intro,True.intro⟩⟩,⟨sg25480,⟨sg25479,True.intro,True.intro⟩,⟨sg25481,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_138All : degreeTree43_138.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25450,degreeTree43_136All,degreeTree43_137All⟩

lemma degreeTree43_139All : degreeTree43_139.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25418,degreeTree43_135All,degreeTree43_138All⟩

lemma degreeTree43_140All : degreeTree43_140.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25353,degreeTree43_130All,degreeTree43_139All⟩

lemma degreeTree43_141All : degreeTree43_141.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25491,⟨sg25487,⟨sg25485,⟨sg25484,⟨sg25483,True.intro,True.intro⟩,True.intro⟩,⟨sg25486,True.intro,True.intro⟩⟩,⟨sg25489,⟨sg25488,True.intro,True.intro⟩,⟨sg25490,True.intro,True.intro⟩⟩⟩,⟨sg25495,⟨sg25493,⟨sg25492,True.intro,True.intro⟩,⟨sg25494,True.intro,True.intro⟩⟩,⟨sg25497,⟨sg25496,True.intro,True.intro⟩,⟨sg25498,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_142All : degreeTree43_142.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25507,⟨sg25503,⟨sg25501,⟨sg25500,True.intro,True.intro⟩,⟨sg25502,True.intro,True.intro⟩⟩,⟨sg25505,⟨sg25504,True.intro,True.intro⟩,⟨sg25506,True.intro,True.intro⟩⟩⟩,⟨sg25511,⟨sg25509,⟨sg25508,True.intro,True.intro⟩,⟨sg25510,True.intro,True.intro⟩⟩,⟨sg25513,⟨sg25512,True.intro,True.intro⟩,⟨sg25514,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_143All : degreeTree43_143.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25499,degreeTree43_141All,degreeTree43_142All⟩

lemma degreeTree43_144All : degreeTree43_144.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25531,⟨sg25523,⟨sg25519,⟨sg25517,⟨sg25516,True.intro,True.intro⟩,⟨sg25518,True.intro,True.intro⟩⟩,⟨sg25521,⟨sg25520,True.intro,True.intro⟩,⟨sg25522,True.intro,True.intro⟩⟩⟩,⟨sg25527,⟨sg25525,⟨sg25524,True.intro,True.intro⟩,⟨sg25526,True.intro,True.intro⟩⟩,⟨sg25529,⟨sg25528,True.intro,True.intro⟩,⟨sg25530,True.intro,True.intro⟩⟩⟩⟩,⟨sg25539,⟨sg25535,⟨sg25533,⟨sg25532,True.intro,True.intro⟩,⟨sg25534,True.intro,True.intro⟩⟩,⟨sg25537,⟨sg25536,True.intro,True.intro⟩,⟨sg25538,True.intro,True.intro⟩⟩⟩,⟨sg25543,⟨sg25541,⟨sg25540,True.intro,True.intro⟩,⟨sg25542,True.intro,True.intro⟩⟩,⟨sg25545,⟨sg25544,True.intro,True.intro⟩,⟨sg25546,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_145All : degreeTree43_145.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25515,degreeTree43_143All,degreeTree43_144All⟩

lemma degreeTree43_146All : degreeTree43_146.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25563,⟨sg25555,⟨sg25551,⟨sg25549,⟨sg25548,True.intro,True.intro⟩,⟨sg25550,True.intro,True.intro⟩⟩,⟨sg25553,⟨sg25552,True.intro,True.intro⟩,⟨sg25554,True.intro,True.intro⟩⟩⟩,⟨sg25559,⟨sg25557,⟨sg25556,True.intro,True.intro⟩,⟨sg25558,True.intro,True.intro⟩⟩,⟨sg25561,⟨sg25560,True.intro,True.intro⟩,⟨sg25562,True.intro,True.intro⟩⟩⟩⟩,⟨sg25571,⟨sg25567,⟨sg25565,⟨sg25564,True.intro,True.intro⟩,⟨sg25566,True.intro,True.intro⟩⟩,⟨sg25569,⟨sg25568,True.intro,True.intro⟩,⟨sg25570,True.intro,True.intro⟩⟩⟩,⟨sg25575,⟨sg25573,⟨sg25572,True.intro,True.intro⟩,⟨sg25574,True.intro,True.intro⟩⟩,⟨sg25577,⟨sg25576,True.intro,True.intro⟩,⟨sg25578,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_147All : degreeTree43_147.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25595,⟨sg25587,⟨sg25583,⟨sg25581,⟨sg25580,True.intro,True.intro⟩,⟨sg25582,True.intro,True.intro⟩⟩,⟨sg25585,⟨sg25584,True.intro,True.intro⟩,⟨sg25586,True.intro,True.intro⟩⟩⟩,⟨sg25591,⟨sg25589,⟨sg25588,True.intro,True.intro⟩,⟨sg25590,True.intro,True.intro⟩⟩,⟨sg25593,⟨sg25592,True.intro,True.intro⟩,⟨sg25594,True.intro,True.intro⟩⟩⟩⟩,⟨sg25603,⟨sg25599,⟨sg25597,⟨sg25596,True.intro,True.intro⟩,⟨sg25598,True.intro,True.intro⟩⟩,⟨sg25601,⟨sg25600,True.intro,True.intro⟩,⟨sg25602,True.intro,True.intro⟩⟩⟩,⟨sg25607,⟨sg25605,⟨sg25604,True.intro,True.intro⟩,⟨sg25606,True.intro,True.intro⟩⟩,⟨sg25609,⟨sg25608,True.intro,True.intro⟩,⟨sg25610,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_148All : degreeTree43_148.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25579,degreeTree43_146All,degreeTree43_147All⟩

lemma degreeTree43_149All : degreeTree43_149.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25547,degreeTree43_145All,degreeTree43_148All⟩

lemma degreeTree43_150All : degreeTree43_150.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25620,⟨sg25616,⟨sg25614,⟨sg25613,⟨sg25612,True.intro,True.intro⟩,True.intro⟩,⟨sg25615,True.intro,True.intro⟩⟩,⟨sg25618,⟨sg25617,True.intro,True.intro⟩,⟨sg25619,True.intro,True.intro⟩⟩⟩,⟨sg25624,⟨sg25622,⟨sg25621,True.intro,True.intro⟩,⟨sg25623,True.intro,True.intro⟩⟩,⟨sg25626,⟨sg25625,True.intro,True.intro⟩,⟨sg25627,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_151All : degreeTree43_151.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25636,⟨sg25632,⟨sg25630,⟨sg25629,True.intro,True.intro⟩,⟨sg25631,True.intro,True.intro⟩⟩,⟨sg25634,⟨sg25633,True.intro,True.intro⟩,⟨sg25635,True.intro,True.intro⟩⟩⟩,⟨sg25640,⟨sg25638,⟨sg25637,True.intro,True.intro⟩,⟨sg25639,True.intro,True.intro⟩⟩,⟨sg25642,⟨sg25641,True.intro,True.intro⟩,⟨sg25643,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_152All : degreeTree43_152.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25628,degreeTree43_150All,degreeTree43_151All⟩

lemma degreeTree43_153All : degreeTree43_153.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25660,⟨sg25652,⟨sg25648,⟨sg25646,⟨sg25645,True.intro,True.intro⟩,⟨sg25647,True.intro,True.intro⟩⟩,⟨sg25650,⟨sg25649,True.intro,True.intro⟩,⟨sg25651,True.intro,True.intro⟩⟩⟩,⟨sg25656,⟨sg25654,⟨sg25653,True.intro,True.intro⟩,⟨sg25655,True.intro,True.intro⟩⟩,⟨sg25658,⟨sg25657,True.intro,True.intro⟩,⟨sg25659,True.intro,True.intro⟩⟩⟩⟩,⟨sg25668,⟨sg25664,⟨sg25662,⟨sg25661,True.intro,True.intro⟩,⟨sg25663,True.intro,True.intro⟩⟩,⟨sg25666,⟨sg25665,True.intro,True.intro⟩,⟨sg25667,True.intro,True.intro⟩⟩⟩,⟨sg25672,⟨sg25670,⟨sg25669,True.intro,True.intro⟩,⟨sg25671,True.intro,True.intro⟩⟩,⟨sg25674,⟨sg25673,True.intro,True.intro⟩,⟨sg25675,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_154All : degreeTree43_154.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25644,degreeTree43_152All,degreeTree43_153All⟩

lemma degreeTree43_155All : degreeTree43_155.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25692,⟨sg25684,⟨sg25680,⟨sg25678,⟨sg25677,True.intro,True.intro⟩,⟨sg25679,True.intro,True.intro⟩⟩,⟨sg25682,⟨sg25681,True.intro,True.intro⟩,⟨sg25683,True.intro,True.intro⟩⟩⟩,⟨sg25688,⟨sg25686,⟨sg25685,True.intro,True.intro⟩,⟨sg25687,True.intro,True.intro⟩⟩,⟨sg25690,⟨sg25689,True.intro,True.intro⟩,⟨sg25691,True.intro,True.intro⟩⟩⟩⟩,⟨sg25700,⟨sg25696,⟨sg25694,⟨sg25693,True.intro,True.intro⟩,⟨sg25695,True.intro,True.intro⟩⟩,⟨sg25698,⟨sg25697,True.intro,True.intro⟩,⟨sg25699,True.intro,True.intro⟩⟩⟩,⟨sg25704,⟨sg25702,⟨sg25701,True.intro,True.intro⟩,⟨sg25703,True.intro,True.intro⟩⟩,⟨sg25706,⟨sg25705,True.intro,True.intro⟩,⟨sg25707,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_156All : degreeTree43_156.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25724,⟨sg25716,⟨sg25712,⟨sg25710,⟨sg25709,True.intro,True.intro⟩,⟨sg25711,True.intro,True.intro⟩⟩,⟨sg25714,⟨sg25713,True.intro,True.intro⟩,⟨sg25715,True.intro,True.intro⟩⟩⟩,⟨sg25720,⟨sg25718,⟨sg25717,True.intro,True.intro⟩,⟨sg25719,True.intro,True.intro⟩⟩,⟨sg25722,⟨sg25721,True.intro,True.intro⟩,⟨sg25723,True.intro,True.intro⟩⟩⟩⟩,⟨sg25732,⟨sg25728,⟨sg25726,⟨sg25725,True.intro,True.intro⟩,⟨sg25727,True.intro,True.intro⟩⟩,⟨sg25730,⟨sg25729,True.intro,True.intro⟩,⟨sg25731,True.intro,True.intro⟩⟩⟩,⟨sg25736,⟨sg25734,⟨sg25733,True.intro,True.intro⟩,⟨sg25735,True.intro,True.intro⟩⟩,⟨sg25738,⟨sg25737,True.intro,True.intro⟩,⟨sg25739,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_157All : degreeTree43_157.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25708,degreeTree43_155All,degreeTree43_156All⟩

lemma degreeTree43_158All : degreeTree43_158.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25676,degreeTree43_154All,degreeTree43_157All⟩

lemma degreeTree43_159All : degreeTree43_159.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25611,degreeTree43_149All,degreeTree43_158All⟩

lemma degreeTree43_160All : degreeTree43_160.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25482,degreeTree43_140All,degreeTree43_159All⟩

lemma degreeTree43_161All : degreeTree43_161.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25224,degreeTree43_121All,degreeTree43_160All⟩

lemma degreeTree43_162All : degreeTree43_162.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg24707,degreeTree43_80All,degreeTree43_161All⟩

lemma degreeTree43_163All : degreeTree43_163.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25749,⟨sg25745,⟨sg25743,⟨sg25742,⟨sg25741,True.intro,True.intro⟩,True.intro⟩,⟨sg25744,True.intro,True.intro⟩⟩,⟨sg25747,⟨sg25746,True.intro,True.intro⟩,⟨sg25748,True.intro,True.intro⟩⟩⟩,⟨sg25753,⟨sg25751,⟨sg25750,True.intro,True.intro⟩,⟨sg25752,True.intro,True.intro⟩⟩,⟨sg25755,⟨sg25754,True.intro,True.intro⟩,⟨sg25756,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_164All : degreeTree43_164.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25765,⟨sg25761,⟨sg25759,⟨sg25758,True.intro,True.intro⟩,⟨sg25760,True.intro,True.intro⟩⟩,⟨sg25763,⟨sg25762,True.intro,True.intro⟩,⟨sg25764,True.intro,True.intro⟩⟩⟩,⟨sg25769,⟨sg25767,⟨sg25766,True.intro,True.intro⟩,⟨sg25768,True.intro,True.intro⟩⟩,⟨sg25771,⟨sg25770,True.intro,True.intro⟩,⟨sg25772,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_165All : degreeTree43_165.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25757,degreeTree43_163All,degreeTree43_164All⟩

lemma degreeTree43_166All : degreeTree43_166.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25789,⟨sg25781,⟨sg25777,⟨sg25775,⟨sg25774,True.intro,True.intro⟩,⟨sg25776,True.intro,True.intro⟩⟩,⟨sg25779,⟨sg25778,True.intro,True.intro⟩,⟨sg25780,True.intro,True.intro⟩⟩⟩,⟨sg25785,⟨sg25783,⟨sg25782,True.intro,True.intro⟩,⟨sg25784,True.intro,True.intro⟩⟩,⟨sg25787,⟨sg25786,True.intro,True.intro⟩,⟨sg25788,True.intro,True.intro⟩⟩⟩⟩,⟨sg25797,⟨sg25793,⟨sg25791,⟨sg25790,True.intro,True.intro⟩,⟨sg25792,True.intro,True.intro⟩⟩,⟨sg25795,⟨sg25794,True.intro,True.intro⟩,⟨sg25796,True.intro,True.intro⟩⟩⟩,⟨sg25801,⟨sg25799,⟨sg25798,True.intro,True.intro⟩,⟨sg25800,True.intro,True.intro⟩⟩,⟨sg25803,⟨sg25802,True.intro,True.intro⟩,⟨sg25804,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_167All : degreeTree43_167.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25773,degreeTree43_165All,degreeTree43_166All⟩

lemma degreeTree43_168All : degreeTree43_168.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25814,⟨sg25810,⟨sg25808,⟨sg25807,⟨sg25806,True.intro,True.intro⟩,True.intro⟩,⟨sg25809,True.intro,True.intro⟩⟩,⟨sg25812,⟨sg25811,True.intro,True.intro⟩,⟨sg25813,True.intro,True.intro⟩⟩⟩,⟨sg25818,⟨sg25816,⟨sg25815,True.intro,True.intro⟩,⟨sg25817,True.intro,True.intro⟩⟩,⟨sg25820,⟨sg25819,True.intro,True.intro⟩,⟨sg25821,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_169All : degreeTree43_169.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25830,⟨sg25826,⟨sg25824,⟨sg25823,True.intro,True.intro⟩,⟨sg25825,True.intro,True.intro⟩⟩,⟨sg25828,⟨sg25827,True.intro,True.intro⟩,⟨sg25829,True.intro,True.intro⟩⟩⟩,⟨sg25834,⟨sg25832,⟨sg25831,True.intro,True.intro⟩,⟨sg25833,True.intro,True.intro⟩⟩,⟨sg25836,⟨sg25835,True.intro,True.intro⟩,⟨sg25837,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_170All : degreeTree43_170.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25822,degreeTree43_168All,degreeTree43_169All⟩

lemma degreeTree43_171All : degreeTree43_171.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25854,⟨sg25846,⟨sg25842,⟨sg25840,⟨sg25839,True.intro,True.intro⟩,⟨sg25841,True.intro,True.intro⟩⟩,⟨sg25844,⟨sg25843,True.intro,True.intro⟩,⟨sg25845,True.intro,True.intro⟩⟩⟩,⟨sg25850,⟨sg25848,⟨sg25847,True.intro,True.intro⟩,⟨sg25849,True.intro,True.intro⟩⟩,⟨sg25852,⟨sg25851,True.intro,True.intro⟩,⟨sg25853,True.intro,True.intro⟩⟩⟩⟩,⟨sg25862,⟨sg25858,⟨sg25856,⟨sg25855,True.intro,True.intro⟩,⟨sg25857,True.intro,True.intro⟩⟩,⟨sg25860,⟨sg25859,True.intro,True.intro⟩,⟨sg25861,True.intro,True.intro⟩⟩⟩,⟨sg25866,⟨sg25864,⟨sg25863,True.intro,True.intro⟩,⟨sg25865,True.intro,True.intro⟩⟩,⟨sg25868,⟨sg25867,True.intro,True.intro⟩,⟨sg25869,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_172All : degreeTree43_172.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25838,degreeTree43_170All,degreeTree43_171All⟩

lemma degreeTree43_173All : degreeTree43_173.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25805,degreeTree43_167All,degreeTree43_172All⟩

lemma degreeTree43_174All : degreeTree43_174.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25879,⟨sg25875,⟨sg25873,⟨sg25872,⟨sg25871,True.intro,True.intro⟩,True.intro⟩,⟨sg25874,True.intro,True.intro⟩⟩,⟨sg25877,⟨sg25876,True.intro,True.intro⟩,⟨sg25878,True.intro,True.intro⟩⟩⟩,⟨sg25883,⟨sg25881,⟨sg25880,True.intro,True.intro⟩,⟨sg25882,True.intro,True.intro⟩⟩,⟨sg25885,⟨sg25884,True.intro,True.intro⟩,⟨sg25886,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_175All : degreeTree43_175.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25895,⟨sg25891,⟨sg25889,⟨sg25888,True.intro,True.intro⟩,⟨sg25890,True.intro,True.intro⟩⟩,⟨sg25893,⟨sg25892,True.intro,True.intro⟩,⟨sg25894,True.intro,True.intro⟩⟩⟩,⟨sg25899,⟨sg25897,⟨sg25896,True.intro,True.intro⟩,⟨sg25898,True.intro,True.intro⟩⟩,⟨sg25901,⟨sg25900,True.intro,True.intro⟩,⟨sg25902,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_176All : degreeTree43_176.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25887,degreeTree43_174All,degreeTree43_175All⟩

lemma degreeTree43_177All : degreeTree43_177.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25919,⟨sg25911,⟨sg25907,⟨sg25905,⟨sg25904,True.intro,True.intro⟩,⟨sg25906,True.intro,True.intro⟩⟩,⟨sg25909,⟨sg25908,True.intro,True.intro⟩,⟨sg25910,True.intro,True.intro⟩⟩⟩,⟨sg25915,⟨sg25913,⟨sg25912,True.intro,True.intro⟩,⟨sg25914,True.intro,True.intro⟩⟩,⟨sg25917,⟨sg25916,True.intro,True.intro⟩,⟨sg25918,True.intro,True.intro⟩⟩⟩⟩,⟨sg25927,⟨sg25923,⟨sg25921,⟨sg25920,True.intro,True.intro⟩,⟨sg25922,True.intro,True.intro⟩⟩,⟨sg25925,⟨sg25924,True.intro,True.intro⟩,⟨sg25926,True.intro,True.intro⟩⟩⟩,⟨sg25931,⟨sg25929,⟨sg25928,True.intro,True.intro⟩,⟨sg25930,True.intro,True.intro⟩⟩,⟨sg25933,⟨sg25932,True.intro,True.intro⟩,⟨sg25934,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_178All : degreeTree43_178.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25903,degreeTree43_176All,degreeTree43_177All⟩

lemma degreeTree43_179All : degreeTree43_179.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25951,⟨sg25943,⟨sg25939,⟨sg25937,⟨sg25936,True.intro,True.intro⟩,⟨sg25938,True.intro,True.intro⟩⟩,⟨sg25941,⟨sg25940,True.intro,True.intro⟩,⟨sg25942,True.intro,True.intro⟩⟩⟩,⟨sg25947,⟨sg25945,⟨sg25944,True.intro,True.intro⟩,⟨sg25946,True.intro,True.intro⟩⟩,⟨sg25949,⟨sg25948,True.intro,True.intro⟩,⟨sg25950,True.intro,True.intro⟩⟩⟩⟩,⟨sg25959,⟨sg25955,⟨sg25953,⟨sg25952,True.intro,True.intro⟩,⟨sg25954,True.intro,True.intro⟩⟩,⟨sg25957,⟨sg25956,True.intro,True.intro⟩,⟨sg25958,True.intro,True.intro⟩⟩⟩,⟨sg25963,⟨sg25961,⟨sg25960,True.intro,True.intro⟩,⟨sg25962,True.intro,True.intro⟩⟩,⟨sg25965,⟨sg25964,True.intro,True.intro⟩,⟨sg25966,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_180All : degreeTree43_180.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25983,⟨sg25975,⟨sg25971,⟨sg25969,⟨sg25968,True.intro,True.intro⟩,⟨sg25970,True.intro,True.intro⟩⟩,⟨sg25973,⟨sg25972,True.intro,True.intro⟩,⟨sg25974,True.intro,True.intro⟩⟩⟩,⟨sg25979,⟨sg25977,⟨sg25976,True.intro,True.intro⟩,⟨sg25978,True.intro,True.intro⟩⟩,⟨sg25981,⟨sg25980,True.intro,True.intro⟩,⟨sg25982,True.intro,True.intro⟩⟩⟩⟩,⟨sg25991,⟨sg25987,⟨sg25985,⟨sg25984,True.intro,True.intro⟩,⟨sg25986,True.intro,True.intro⟩⟩,⟨sg25989,⟨sg25988,True.intro,True.intro⟩,⟨sg25990,True.intro,True.intro⟩⟩⟩,⟨sg25995,⟨sg25993,⟨sg25992,True.intro,True.intro⟩,⟨sg25994,True.intro,True.intro⟩⟩,⟨sg25997,⟨sg25996,True.intro,True.intro⟩,⟨sg25998,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_181All : degreeTree43_181.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25967,degreeTree43_179All,degreeTree43_180All⟩

lemma degreeTree43_182All : degreeTree43_182.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25935,degreeTree43_178All,degreeTree43_181All⟩

lemma degreeTree43_183All : degreeTree43_183.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25870,degreeTree43_173All,degreeTree43_182All⟩

lemma degreeTree43_184All : degreeTree43_184.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26008,⟨sg26004,⟨sg26002,⟨sg26001,⟨sg26000,True.intro,True.intro⟩,True.intro⟩,⟨sg26003,True.intro,True.intro⟩⟩,⟨sg26006,⟨sg26005,True.intro,True.intro⟩,⟨sg26007,True.intro,True.intro⟩⟩⟩,⟨sg26012,⟨sg26010,⟨sg26009,True.intro,True.intro⟩,⟨sg26011,True.intro,True.intro⟩⟩,⟨sg26014,⟨sg26013,True.intro,True.intro⟩,⟨sg26015,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_185All : degreeTree43_185.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26024,⟨sg26020,⟨sg26018,⟨sg26017,True.intro,True.intro⟩,⟨sg26019,True.intro,True.intro⟩⟩,⟨sg26022,⟨sg26021,True.intro,True.intro⟩,⟨sg26023,True.intro,True.intro⟩⟩⟩,⟨sg26028,⟨sg26026,⟨sg26025,True.intro,True.intro⟩,⟨sg26027,True.intro,True.intro⟩⟩,⟨sg26030,⟨sg26029,True.intro,True.intro⟩,⟨sg26031,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_186All : degreeTree43_186.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26016,degreeTree43_184All,degreeTree43_185All⟩

lemma degreeTree43_187All : degreeTree43_187.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26048,⟨sg26040,⟨sg26036,⟨sg26034,⟨sg26033,True.intro,True.intro⟩,⟨sg26035,True.intro,True.intro⟩⟩,⟨sg26038,⟨sg26037,True.intro,True.intro⟩,⟨sg26039,True.intro,True.intro⟩⟩⟩,⟨sg26044,⟨sg26042,⟨sg26041,True.intro,True.intro⟩,⟨sg26043,True.intro,True.intro⟩⟩,⟨sg26046,⟨sg26045,True.intro,True.intro⟩,⟨sg26047,True.intro,True.intro⟩⟩⟩⟩,⟨sg26056,⟨sg26052,⟨sg26050,⟨sg26049,True.intro,True.intro⟩,⟨sg26051,True.intro,True.intro⟩⟩,⟨sg26054,⟨sg26053,True.intro,True.intro⟩,⟨sg26055,True.intro,True.intro⟩⟩⟩,⟨sg26060,⟨sg26058,⟨sg26057,True.intro,True.intro⟩,⟨sg26059,True.intro,True.intro⟩⟩,⟨sg26062,⟨sg26061,True.intro,True.intro⟩,⟨sg26063,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_188All : degreeTree43_188.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26032,degreeTree43_186All,degreeTree43_187All⟩

lemma degreeTree43_189All : degreeTree43_189.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26080,⟨sg26072,⟨sg26068,⟨sg26066,⟨sg26065,True.intro,True.intro⟩,⟨sg26067,True.intro,True.intro⟩⟩,⟨sg26070,⟨sg26069,True.intro,True.intro⟩,⟨sg26071,True.intro,True.intro⟩⟩⟩,⟨sg26076,⟨sg26074,⟨sg26073,True.intro,True.intro⟩,⟨sg26075,True.intro,True.intro⟩⟩,⟨sg26078,⟨sg26077,True.intro,True.intro⟩,⟨sg26079,True.intro,True.intro⟩⟩⟩⟩,⟨sg26088,⟨sg26084,⟨sg26082,⟨sg26081,True.intro,True.intro⟩,⟨sg26083,True.intro,True.intro⟩⟩,⟨sg26086,⟨sg26085,True.intro,True.intro⟩,⟨sg26087,True.intro,True.intro⟩⟩⟩,⟨sg26092,⟨sg26090,⟨sg26089,True.intro,True.intro⟩,⟨sg26091,True.intro,True.intro⟩⟩,⟨sg26094,⟨sg26093,True.intro,True.intro⟩,⟨sg26095,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_190All : degreeTree43_190.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26112,⟨sg26104,⟨sg26100,⟨sg26098,⟨sg26097,True.intro,True.intro⟩,⟨sg26099,True.intro,True.intro⟩⟩,⟨sg26102,⟨sg26101,True.intro,True.intro⟩,⟨sg26103,True.intro,True.intro⟩⟩⟩,⟨sg26108,⟨sg26106,⟨sg26105,True.intro,True.intro⟩,⟨sg26107,True.intro,True.intro⟩⟩,⟨sg26110,⟨sg26109,True.intro,True.intro⟩,⟨sg26111,True.intro,True.intro⟩⟩⟩⟩,⟨sg26120,⟨sg26116,⟨sg26114,⟨sg26113,True.intro,True.intro⟩,⟨sg26115,True.intro,True.intro⟩⟩,⟨sg26118,⟨sg26117,True.intro,True.intro⟩,⟨sg26119,True.intro,True.intro⟩⟩⟩,⟨sg26124,⟨sg26122,⟨sg26121,True.intro,True.intro⟩,⟨sg26123,True.intro,True.intro⟩⟩,⟨sg26126,⟨sg26125,True.intro,True.intro⟩,⟨sg26127,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_191All : degreeTree43_191.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26096,degreeTree43_189All,degreeTree43_190All⟩

lemma degreeTree43_192All : degreeTree43_192.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26064,degreeTree43_188All,degreeTree43_191All⟩

lemma degreeTree43_193All : degreeTree43_193.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26137,⟨sg26133,⟨sg26131,⟨sg26130,⟨sg26129,True.intro,True.intro⟩,True.intro⟩,⟨sg26132,True.intro,True.intro⟩⟩,⟨sg26135,⟨sg26134,True.intro,True.intro⟩,⟨sg26136,True.intro,True.intro⟩⟩⟩,⟨sg26141,⟨sg26139,⟨sg26138,True.intro,True.intro⟩,⟨sg26140,True.intro,True.intro⟩⟩,⟨sg26143,⟨sg26142,True.intro,True.intro⟩,⟨sg26144,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_194All : degreeTree43_194.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26153,⟨sg26149,⟨sg26147,⟨sg26146,True.intro,True.intro⟩,⟨sg26148,True.intro,True.intro⟩⟩,⟨sg26151,⟨sg26150,True.intro,True.intro⟩,⟨sg26152,True.intro,True.intro⟩⟩⟩,⟨sg26157,⟨sg26155,⟨sg26154,True.intro,True.intro⟩,⟨sg26156,True.intro,True.intro⟩⟩,⟨sg26159,⟨sg26158,True.intro,True.intro⟩,⟨sg26160,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_195All : degreeTree43_195.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26145,degreeTree43_193All,degreeTree43_194All⟩

lemma degreeTree43_196All : degreeTree43_196.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26177,⟨sg26169,⟨sg26165,⟨sg26163,⟨sg26162,True.intro,True.intro⟩,⟨sg26164,True.intro,True.intro⟩⟩,⟨sg26167,⟨sg26166,True.intro,True.intro⟩,⟨sg26168,True.intro,True.intro⟩⟩⟩,⟨sg26173,⟨sg26171,⟨sg26170,True.intro,True.intro⟩,⟨sg26172,True.intro,True.intro⟩⟩,⟨sg26175,⟨sg26174,True.intro,True.intro⟩,⟨sg26176,True.intro,True.intro⟩⟩⟩⟩,⟨sg26185,⟨sg26181,⟨sg26179,⟨sg26178,True.intro,True.intro⟩,⟨sg26180,True.intro,True.intro⟩⟩,⟨sg26183,⟨sg26182,True.intro,True.intro⟩,⟨sg26184,True.intro,True.intro⟩⟩⟩,⟨sg26189,⟨sg26187,⟨sg26186,True.intro,True.intro⟩,⟨sg26188,True.intro,True.intro⟩⟩,⟨sg26191,⟨sg26190,True.intro,True.intro⟩,⟨sg26192,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_197All : degreeTree43_197.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26161,degreeTree43_195All,degreeTree43_196All⟩

lemma degreeTree43_198All : degreeTree43_198.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26209,⟨sg26201,⟨sg26197,⟨sg26195,⟨sg26194,True.intro,True.intro⟩,⟨sg26196,True.intro,True.intro⟩⟩,⟨sg26199,⟨sg26198,True.intro,True.intro⟩,⟨sg26200,True.intro,True.intro⟩⟩⟩,⟨sg26205,⟨sg26203,⟨sg26202,True.intro,True.intro⟩,⟨sg26204,True.intro,True.intro⟩⟩,⟨sg26207,⟨sg26206,True.intro,True.intro⟩,⟨sg26208,True.intro,True.intro⟩⟩⟩⟩,⟨sg26217,⟨sg26213,⟨sg26211,⟨sg26210,True.intro,True.intro⟩,⟨sg26212,True.intro,True.intro⟩⟩,⟨sg26215,⟨sg26214,True.intro,True.intro⟩,⟨sg26216,True.intro,True.intro⟩⟩⟩,⟨sg26221,⟨sg26219,⟨sg26218,True.intro,True.intro⟩,⟨sg26220,True.intro,True.intro⟩⟩,⟨sg26223,⟨sg26222,True.intro,True.intro⟩,⟨sg26224,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_199All : degreeTree43_199.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26241,⟨sg26233,⟨sg26229,⟨sg26227,⟨sg26226,True.intro,True.intro⟩,⟨sg26228,True.intro,True.intro⟩⟩,⟨sg26231,⟨sg26230,True.intro,True.intro⟩,⟨sg26232,True.intro,True.intro⟩⟩⟩,⟨sg26237,⟨sg26235,⟨sg26234,True.intro,True.intro⟩,⟨sg26236,True.intro,True.intro⟩⟩,⟨sg26239,⟨sg26238,True.intro,True.intro⟩,⟨sg26240,True.intro,True.intro⟩⟩⟩⟩,⟨sg26249,⟨sg26245,⟨sg26243,⟨sg26242,True.intro,True.intro⟩,⟨sg26244,True.intro,True.intro⟩⟩,⟨sg26247,⟨sg26246,True.intro,True.intro⟩,⟨sg26248,True.intro,True.intro⟩⟩⟩,⟨sg26253,⟨sg26251,⟨sg26250,True.intro,True.intro⟩,⟨sg26252,True.intro,True.intro⟩⟩,⟨sg26255,⟨sg26254,True.intro,True.intro⟩,⟨sg26256,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_200All : degreeTree43_200.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26225,degreeTree43_198All,degreeTree43_199All⟩

lemma degreeTree43_201All : degreeTree43_201.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26193,degreeTree43_197All,degreeTree43_200All⟩

lemma degreeTree43_202All : degreeTree43_202.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26128,degreeTree43_192All,degreeTree43_201All⟩

lemma degreeTree43_203All : degreeTree43_203.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25999,degreeTree43_183All,degreeTree43_202All⟩

lemma degreeTree43_204All : degreeTree43_204.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26266,⟨sg26262,⟨sg26260,⟨sg26259,⟨sg26258,True.intro,True.intro⟩,True.intro⟩,⟨sg26261,True.intro,True.intro⟩⟩,⟨sg26264,⟨sg26263,True.intro,True.intro⟩,⟨sg26265,True.intro,True.intro⟩⟩⟩,⟨sg26270,⟨sg26268,⟨sg26267,True.intro,True.intro⟩,⟨sg26269,True.intro,True.intro⟩⟩,⟨sg26272,⟨sg26271,True.intro,True.intro⟩,⟨sg26273,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_205All : degreeTree43_205.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26282,⟨sg26278,⟨sg26276,⟨sg26275,True.intro,True.intro⟩,⟨sg26277,True.intro,True.intro⟩⟩,⟨sg26280,⟨sg26279,True.intro,True.intro⟩,⟨sg26281,True.intro,True.intro⟩⟩⟩,⟨sg26286,⟨sg26284,⟨sg26283,True.intro,True.intro⟩,⟨sg26285,True.intro,True.intro⟩⟩,⟨sg26288,⟨sg26287,True.intro,True.intro⟩,⟨sg26289,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_206All : degreeTree43_206.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26274,degreeTree43_204All,degreeTree43_205All⟩

lemma degreeTree43_207All : degreeTree43_207.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26306,⟨sg26298,⟨sg26294,⟨sg26292,⟨sg26291,True.intro,True.intro⟩,⟨sg26293,True.intro,True.intro⟩⟩,⟨sg26296,⟨sg26295,True.intro,True.intro⟩,⟨sg26297,True.intro,True.intro⟩⟩⟩,⟨sg26302,⟨sg26300,⟨sg26299,True.intro,True.intro⟩,⟨sg26301,True.intro,True.intro⟩⟩,⟨sg26304,⟨sg26303,True.intro,True.intro⟩,⟨sg26305,True.intro,True.intro⟩⟩⟩⟩,⟨sg26314,⟨sg26310,⟨sg26308,⟨sg26307,True.intro,True.intro⟩,⟨sg26309,True.intro,True.intro⟩⟩,⟨sg26312,⟨sg26311,True.intro,True.intro⟩,⟨sg26313,True.intro,True.intro⟩⟩⟩,⟨sg26318,⟨sg26316,⟨sg26315,True.intro,True.intro⟩,⟨sg26317,True.intro,True.intro⟩⟩,⟨sg26320,⟨sg26319,True.intro,True.intro⟩,⟨sg26321,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_208All : degreeTree43_208.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26290,degreeTree43_206All,degreeTree43_207All⟩

lemma degreeTree43_209All : degreeTree43_209.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26338,⟨sg26330,⟨sg26326,⟨sg26324,⟨sg26323,True.intro,True.intro⟩,⟨sg26325,True.intro,True.intro⟩⟩,⟨sg26328,⟨sg26327,True.intro,True.intro⟩,⟨sg26329,True.intro,True.intro⟩⟩⟩,⟨sg26334,⟨sg26332,⟨sg26331,True.intro,True.intro⟩,⟨sg26333,True.intro,True.intro⟩⟩,⟨sg26336,⟨sg26335,True.intro,True.intro⟩,⟨sg26337,True.intro,True.intro⟩⟩⟩⟩,⟨sg26346,⟨sg26342,⟨sg26340,⟨sg26339,True.intro,True.intro⟩,⟨sg26341,True.intro,True.intro⟩⟩,⟨sg26344,⟨sg26343,True.intro,True.intro⟩,⟨sg26345,True.intro,True.intro⟩⟩⟩,⟨sg26350,⟨sg26348,⟨sg26347,True.intro,True.intro⟩,⟨sg26349,True.intro,True.intro⟩⟩,⟨sg26352,⟨sg26351,True.intro,True.intro⟩,⟨sg26353,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_210All : degreeTree43_210.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26370,⟨sg26362,⟨sg26358,⟨sg26356,⟨sg26355,True.intro,True.intro⟩,⟨sg26357,True.intro,True.intro⟩⟩,⟨sg26360,⟨sg26359,True.intro,True.intro⟩,⟨sg26361,True.intro,True.intro⟩⟩⟩,⟨sg26366,⟨sg26364,⟨sg26363,True.intro,True.intro⟩,⟨sg26365,True.intro,True.intro⟩⟩,⟨sg26368,⟨sg26367,True.intro,True.intro⟩,⟨sg26369,True.intro,True.intro⟩⟩⟩⟩,⟨sg26378,⟨sg26374,⟨sg26372,⟨sg26371,True.intro,True.intro⟩,⟨sg26373,True.intro,True.intro⟩⟩,⟨sg26376,⟨sg26375,True.intro,True.intro⟩,⟨sg26377,True.intro,True.intro⟩⟩⟩,⟨sg26382,⟨sg26380,⟨sg26379,True.intro,True.intro⟩,⟨sg26381,True.intro,True.intro⟩⟩,⟨sg26384,⟨sg26383,True.intro,True.intro⟩,⟨sg26385,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_211All : degreeTree43_211.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26354,degreeTree43_209All,degreeTree43_210All⟩

lemma degreeTree43_212All : degreeTree43_212.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26322,degreeTree43_208All,degreeTree43_211All⟩

lemma degreeTree43_213All : degreeTree43_213.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26395,⟨sg26391,⟨sg26389,⟨sg26388,⟨sg26387,True.intro,True.intro⟩,True.intro⟩,⟨sg26390,True.intro,True.intro⟩⟩,⟨sg26393,⟨sg26392,True.intro,True.intro⟩,⟨sg26394,True.intro,True.intro⟩⟩⟩,⟨sg26399,⟨sg26397,⟨sg26396,True.intro,True.intro⟩,⟨sg26398,True.intro,True.intro⟩⟩,⟨sg26401,⟨sg26400,True.intro,True.intro⟩,⟨sg26402,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_214All : degreeTree43_214.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26411,⟨sg26407,⟨sg26405,⟨sg26404,True.intro,True.intro⟩,⟨sg26406,True.intro,True.intro⟩⟩,⟨sg26409,⟨sg26408,True.intro,True.intro⟩,⟨sg26410,True.intro,True.intro⟩⟩⟩,⟨sg26415,⟨sg26413,⟨sg26412,True.intro,True.intro⟩,⟨sg26414,True.intro,True.intro⟩⟩,⟨sg26417,⟨sg26416,True.intro,True.intro⟩,⟨sg26418,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_215All : degreeTree43_215.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26403,degreeTree43_213All,degreeTree43_214All⟩

lemma degreeTree43_216All : degreeTree43_216.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26435,⟨sg26427,⟨sg26423,⟨sg26421,⟨sg26420,True.intro,True.intro⟩,⟨sg26422,True.intro,True.intro⟩⟩,⟨sg26425,⟨sg26424,True.intro,True.intro⟩,⟨sg26426,True.intro,True.intro⟩⟩⟩,⟨sg26431,⟨sg26429,⟨sg26428,True.intro,True.intro⟩,⟨sg26430,True.intro,True.intro⟩⟩,⟨sg26433,⟨sg26432,True.intro,True.intro⟩,⟨sg26434,True.intro,True.intro⟩⟩⟩⟩,⟨sg26443,⟨sg26439,⟨sg26437,⟨sg26436,True.intro,True.intro⟩,⟨sg26438,True.intro,True.intro⟩⟩,⟨sg26441,⟨sg26440,True.intro,True.intro⟩,⟨sg26442,True.intro,True.intro⟩⟩⟩,⟨sg26447,⟨sg26445,⟨sg26444,True.intro,True.intro⟩,⟨sg26446,True.intro,True.intro⟩⟩,⟨sg26449,⟨sg26448,True.intro,True.intro⟩,⟨sg26450,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_217All : degreeTree43_217.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26419,degreeTree43_215All,degreeTree43_216All⟩

lemma degreeTree43_218All : degreeTree43_218.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26467,⟨sg26459,⟨sg26455,⟨sg26453,⟨sg26452,True.intro,True.intro⟩,⟨sg26454,True.intro,True.intro⟩⟩,⟨sg26457,⟨sg26456,True.intro,True.intro⟩,⟨sg26458,True.intro,True.intro⟩⟩⟩,⟨sg26463,⟨sg26461,⟨sg26460,True.intro,True.intro⟩,⟨sg26462,True.intro,True.intro⟩⟩,⟨sg26465,⟨sg26464,True.intro,True.intro⟩,⟨sg26466,True.intro,True.intro⟩⟩⟩⟩,⟨sg26475,⟨sg26471,⟨sg26469,⟨sg26468,True.intro,True.intro⟩,⟨sg26470,True.intro,True.intro⟩⟩,⟨sg26473,⟨sg26472,True.intro,True.intro⟩,⟨sg26474,True.intro,True.intro⟩⟩⟩,⟨sg26479,⟨sg26477,⟨sg26476,True.intro,True.intro⟩,⟨sg26478,True.intro,True.intro⟩⟩,⟨sg26481,⟨sg26480,True.intro,True.intro⟩,⟨sg26482,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_219All : degreeTree43_219.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26499,⟨sg26491,⟨sg26487,⟨sg26485,⟨sg26484,True.intro,True.intro⟩,⟨sg26486,True.intro,True.intro⟩⟩,⟨sg26489,⟨sg26488,True.intro,True.intro⟩,⟨sg26490,True.intro,True.intro⟩⟩⟩,⟨sg26495,⟨sg26493,⟨sg26492,True.intro,True.intro⟩,⟨sg26494,True.intro,True.intro⟩⟩,⟨sg26497,⟨sg26496,True.intro,True.intro⟩,⟨sg26498,True.intro,True.intro⟩⟩⟩⟩,⟨sg26507,⟨sg26503,⟨sg26501,⟨sg26500,True.intro,True.intro⟩,⟨sg26502,True.intro,True.intro⟩⟩,⟨sg26505,⟨sg26504,True.intro,True.intro⟩,⟨sg26506,True.intro,True.intro⟩⟩⟩,⟨sg26511,⟨sg26509,⟨sg26508,True.intro,True.intro⟩,⟨sg26510,True.intro,True.intro⟩⟩,⟨sg26513,⟨sg26512,True.intro,True.intro⟩,⟨sg26514,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_220All : degreeTree43_220.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26483,degreeTree43_218All,degreeTree43_219All⟩

lemma degreeTree43_221All : degreeTree43_221.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26451,degreeTree43_217All,degreeTree43_220All⟩

lemma degreeTree43_222All : degreeTree43_222.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26386,degreeTree43_212All,degreeTree43_221All⟩

lemma degreeTree43_223All : degreeTree43_223.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26524,⟨sg26520,⟨sg26518,⟨sg26517,⟨sg26516,True.intro,True.intro⟩,True.intro⟩,⟨sg26519,True.intro,True.intro⟩⟩,⟨sg26522,⟨sg26521,True.intro,True.intro⟩,⟨sg26523,True.intro,True.intro⟩⟩⟩,⟨sg26528,⟨sg26526,⟨sg26525,True.intro,True.intro⟩,⟨sg26527,True.intro,True.intro⟩⟩,⟨sg26530,⟨sg26529,True.intro,True.intro⟩,⟨sg26531,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_224All : degreeTree43_224.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26540,⟨sg26536,⟨sg26534,⟨sg26533,True.intro,True.intro⟩,⟨sg26535,True.intro,True.intro⟩⟩,⟨sg26538,⟨sg26537,True.intro,True.intro⟩,⟨sg26539,True.intro,True.intro⟩⟩⟩,⟨sg26544,⟨sg26542,⟨sg26541,True.intro,True.intro⟩,⟨sg26543,True.intro,True.intro⟩⟩,⟨sg26546,⟨sg26545,True.intro,True.intro⟩,⟨sg26547,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_225All : degreeTree43_225.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26532,degreeTree43_223All,degreeTree43_224All⟩

lemma degreeTree43_226All : degreeTree43_226.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26564,⟨sg26556,⟨sg26552,⟨sg26550,⟨sg26549,True.intro,True.intro⟩,⟨sg26551,True.intro,True.intro⟩⟩,⟨sg26554,⟨sg26553,True.intro,True.intro⟩,⟨sg26555,True.intro,True.intro⟩⟩⟩,⟨sg26560,⟨sg26558,⟨sg26557,True.intro,True.intro⟩,⟨sg26559,True.intro,True.intro⟩⟩,⟨sg26562,⟨sg26561,True.intro,True.intro⟩,⟨sg26563,True.intro,True.intro⟩⟩⟩⟩,⟨sg26572,⟨sg26568,⟨sg26566,⟨sg26565,True.intro,True.intro⟩,⟨sg26567,True.intro,True.intro⟩⟩,⟨sg26570,⟨sg26569,True.intro,True.intro⟩,⟨sg26571,True.intro,True.intro⟩⟩⟩,⟨sg26576,⟨sg26574,⟨sg26573,True.intro,True.intro⟩,⟨sg26575,True.intro,True.intro⟩⟩,⟨sg26578,⟨sg26577,True.intro,True.intro⟩,⟨sg26579,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_227All : degreeTree43_227.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26548,degreeTree43_225All,degreeTree43_226All⟩

lemma degreeTree43_228All : degreeTree43_228.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26596,⟨sg26588,⟨sg26584,⟨sg26582,⟨sg26581,True.intro,True.intro⟩,⟨sg26583,True.intro,True.intro⟩⟩,⟨sg26586,⟨sg26585,True.intro,True.intro⟩,⟨sg26587,True.intro,True.intro⟩⟩⟩,⟨sg26592,⟨sg26590,⟨sg26589,True.intro,True.intro⟩,⟨sg26591,True.intro,True.intro⟩⟩,⟨sg26594,⟨sg26593,True.intro,True.intro⟩,⟨sg26595,True.intro,True.intro⟩⟩⟩⟩,⟨sg26604,⟨sg26600,⟨sg26598,⟨sg26597,True.intro,True.intro⟩,⟨sg26599,True.intro,True.intro⟩⟩,⟨sg26602,⟨sg26601,True.intro,True.intro⟩,⟨sg26603,True.intro,True.intro⟩⟩⟩,⟨sg26608,⟨sg26606,⟨sg26605,True.intro,True.intro⟩,⟨sg26607,True.intro,True.intro⟩⟩,⟨sg26610,⟨sg26609,True.intro,True.intro⟩,⟨sg26611,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_229All : degreeTree43_229.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26628,⟨sg26620,⟨sg26616,⟨sg26614,⟨sg26613,True.intro,True.intro⟩,⟨sg26615,True.intro,True.intro⟩⟩,⟨sg26618,⟨sg26617,True.intro,True.intro⟩,⟨sg26619,True.intro,True.intro⟩⟩⟩,⟨sg26624,⟨sg26622,⟨sg26621,True.intro,True.intro⟩,⟨sg26623,True.intro,True.intro⟩⟩,⟨sg26626,⟨sg26625,True.intro,True.intro⟩,⟨sg26627,True.intro,True.intro⟩⟩⟩⟩,⟨sg26636,⟨sg26632,⟨sg26630,⟨sg26629,True.intro,True.intro⟩,⟨sg26631,True.intro,True.intro⟩⟩,⟨sg26634,⟨sg26633,True.intro,True.intro⟩,⟨sg26635,True.intro,True.intro⟩⟩⟩,⟨sg26640,⟨sg26638,⟨sg26637,True.intro,True.intro⟩,⟨sg26639,True.intro,True.intro⟩⟩,⟨sg26642,⟨sg26641,True.intro,True.intro⟩,⟨sg26643,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_230All : degreeTree43_230.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26612,degreeTree43_228All,degreeTree43_229All⟩

lemma degreeTree43_231All : degreeTree43_231.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26580,degreeTree43_227All,degreeTree43_230All⟩

lemma degreeTree43_232All : degreeTree43_232.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26653,⟨sg26649,⟨sg26647,⟨sg26646,⟨sg26645,True.intro,True.intro⟩,True.intro⟩,⟨sg26648,True.intro,True.intro⟩⟩,⟨sg26651,⟨sg26650,True.intro,True.intro⟩,⟨sg26652,True.intro,True.intro⟩⟩⟩,⟨sg26657,⟨sg26655,⟨sg26654,True.intro,True.intro⟩,⟨sg26656,True.intro,True.intro⟩⟩,⟨sg26659,⟨sg26658,True.intro,True.intro⟩,⟨sg26660,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_233All : degreeTree43_233.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26669,⟨sg26665,⟨sg26663,⟨sg26662,True.intro,True.intro⟩,⟨sg26664,True.intro,True.intro⟩⟩,⟨sg26667,⟨sg26666,True.intro,True.intro⟩,⟨sg26668,True.intro,True.intro⟩⟩⟩,⟨sg26673,⟨sg26671,⟨sg26670,True.intro,True.intro⟩,⟨sg26672,True.intro,True.intro⟩⟩,⟨sg26675,⟨sg26674,True.intro,True.intro⟩,⟨sg26676,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_234All : degreeTree43_234.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26661,degreeTree43_232All,degreeTree43_233All⟩

lemma degreeTree43_235All : degreeTree43_235.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26693,⟨sg26685,⟨sg26681,⟨sg26679,⟨sg26678,True.intro,True.intro⟩,⟨sg26680,True.intro,True.intro⟩⟩,⟨sg26683,⟨sg26682,True.intro,True.intro⟩,⟨sg26684,True.intro,True.intro⟩⟩⟩,⟨sg26689,⟨sg26687,⟨sg26686,True.intro,True.intro⟩,⟨sg26688,True.intro,True.intro⟩⟩,⟨sg26691,⟨sg26690,True.intro,True.intro⟩,⟨sg26692,True.intro,True.intro⟩⟩⟩⟩,⟨sg26701,⟨sg26697,⟨sg26695,⟨sg26694,True.intro,True.intro⟩,⟨sg26696,True.intro,True.intro⟩⟩,⟨sg26699,⟨sg26698,True.intro,True.intro⟩,⟨sg26700,True.intro,True.intro⟩⟩⟩,⟨sg26705,⟨sg26703,⟨sg26702,True.intro,True.intro⟩,⟨sg26704,True.intro,True.intro⟩⟩,⟨sg26707,⟨sg26706,True.intro,True.intro⟩,⟨sg26708,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_236All : degreeTree43_236.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26677,degreeTree43_234All,degreeTree43_235All⟩

lemma degreeTree43_237All : degreeTree43_237.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26725,⟨sg26717,⟨sg26713,⟨sg26711,⟨sg26710,True.intro,True.intro⟩,⟨sg26712,True.intro,True.intro⟩⟩,⟨sg26715,⟨sg26714,True.intro,True.intro⟩,⟨sg26716,True.intro,True.intro⟩⟩⟩,⟨sg26721,⟨sg26719,⟨sg26718,True.intro,True.intro⟩,⟨sg26720,True.intro,True.intro⟩⟩,⟨sg26723,⟨sg26722,True.intro,True.intro⟩,⟨sg26724,True.intro,True.intro⟩⟩⟩⟩,⟨sg26733,⟨sg26729,⟨sg26727,⟨sg26726,True.intro,True.intro⟩,⟨sg26728,True.intro,True.intro⟩⟩,⟨sg26731,⟨sg26730,True.intro,True.intro⟩,⟨sg26732,True.intro,True.intro⟩⟩⟩,⟨sg26737,⟨sg26735,⟨sg26734,True.intro,True.intro⟩,⟨sg26736,True.intro,True.intro⟩⟩,⟨sg26739,⟨sg26738,True.intro,True.intro⟩,⟨sg26740,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_238All : degreeTree43_238.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26757,⟨sg26749,⟨sg26745,⟨sg26743,⟨sg26742,True.intro,True.intro⟩,⟨sg26744,True.intro,True.intro⟩⟩,⟨sg26747,⟨sg26746,True.intro,True.intro⟩,⟨sg26748,True.intro,True.intro⟩⟩⟩,⟨sg26753,⟨sg26751,⟨sg26750,True.intro,True.intro⟩,⟨sg26752,True.intro,True.intro⟩⟩,⟨sg26755,⟨sg26754,True.intro,True.intro⟩,⟨sg26756,True.intro,True.intro⟩⟩⟩⟩,⟨sg26765,⟨sg26761,⟨sg26759,⟨sg26758,True.intro,True.intro⟩,⟨sg26760,True.intro,True.intro⟩⟩,⟨sg26763,⟨sg26762,True.intro,True.intro⟩,⟨sg26764,True.intro,True.intro⟩⟩⟩,⟨sg26769,⟨sg26767,⟨sg26766,True.intro,True.intro⟩,⟨sg26768,True.intro,True.intro⟩⟩,⟨sg26771,⟨sg26770,True.intro,True.intro⟩,⟨sg26772,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_239All : degreeTree43_239.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26741,degreeTree43_237All,degreeTree43_238All⟩

lemma degreeTree43_240All : degreeTree43_240.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26709,degreeTree43_236All,degreeTree43_239All⟩

lemma degreeTree43_241All : degreeTree43_241.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26644,degreeTree43_231All,degreeTree43_240All⟩

lemma degreeTree43_242All : degreeTree43_242.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26515,degreeTree43_222All,degreeTree43_241All⟩

lemma degreeTree43_243All : degreeTree43_243.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26257,degreeTree43_203All,degreeTree43_242All⟩

lemma degreeTree43_244All : degreeTree43_244.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26782,⟨sg26778,⟨sg26776,⟨sg26775,⟨sg26774,True.intro,True.intro⟩,True.intro⟩,⟨sg26777,True.intro,True.intro⟩⟩,⟨sg26780,⟨sg26779,True.intro,True.intro⟩,⟨sg26781,True.intro,True.intro⟩⟩⟩,⟨sg26786,⟨sg26784,⟨sg26783,True.intro,True.intro⟩,⟨sg26785,True.intro,True.intro⟩⟩,⟨sg26788,⟨sg26787,True.intro,True.intro⟩,⟨sg26789,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_245All : degreeTree43_245.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26798,⟨sg26794,⟨sg26792,⟨sg26791,True.intro,True.intro⟩,⟨sg26793,True.intro,True.intro⟩⟩,⟨sg26796,⟨sg26795,True.intro,True.intro⟩,⟨sg26797,True.intro,True.intro⟩⟩⟩,⟨sg26802,⟨sg26800,⟨sg26799,True.intro,True.intro⟩,⟨sg26801,True.intro,True.intro⟩⟩,⟨sg26804,⟨sg26803,True.intro,True.intro⟩,⟨sg26805,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_246All : degreeTree43_246.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26790,degreeTree43_244All,degreeTree43_245All⟩

lemma degreeTree43_247All : degreeTree43_247.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26822,⟨sg26814,⟨sg26810,⟨sg26808,⟨sg26807,True.intro,True.intro⟩,⟨sg26809,True.intro,True.intro⟩⟩,⟨sg26812,⟨sg26811,True.intro,True.intro⟩,⟨sg26813,True.intro,True.intro⟩⟩⟩,⟨sg26818,⟨sg26816,⟨sg26815,True.intro,True.intro⟩,⟨sg26817,True.intro,True.intro⟩⟩,⟨sg26820,⟨sg26819,True.intro,True.intro⟩,⟨sg26821,True.intro,True.intro⟩⟩⟩⟩,⟨sg26830,⟨sg26826,⟨sg26824,⟨sg26823,True.intro,True.intro⟩,⟨sg26825,True.intro,True.intro⟩⟩,⟨sg26828,⟨sg26827,True.intro,True.intro⟩,⟨sg26829,True.intro,True.intro⟩⟩⟩,⟨sg26834,⟨sg26832,⟨sg26831,True.intro,True.intro⟩,⟨sg26833,True.intro,True.intro⟩⟩,⟨sg26836,⟨sg26835,True.intro,True.intro⟩,⟨sg26837,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_248All : degreeTree43_248.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26806,degreeTree43_246All,degreeTree43_247All⟩

lemma degreeTree43_249All : degreeTree43_249.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26854,⟨sg26846,⟨sg26842,⟨sg26840,⟨sg26839,True.intro,True.intro⟩,⟨sg26841,True.intro,True.intro⟩⟩,⟨sg26844,⟨sg26843,True.intro,True.intro⟩,⟨sg26845,True.intro,True.intro⟩⟩⟩,⟨sg26850,⟨sg26848,⟨sg26847,True.intro,True.intro⟩,⟨sg26849,True.intro,True.intro⟩⟩,⟨sg26852,⟨sg26851,True.intro,True.intro⟩,⟨sg26853,True.intro,True.intro⟩⟩⟩⟩,⟨sg26862,⟨sg26858,⟨sg26856,⟨sg26855,True.intro,True.intro⟩,⟨sg26857,True.intro,True.intro⟩⟩,⟨sg26860,⟨sg26859,True.intro,True.intro⟩,⟨sg26861,True.intro,True.intro⟩⟩⟩,⟨sg26866,⟨sg26864,⟨sg26863,True.intro,True.intro⟩,⟨sg26865,True.intro,True.intro⟩⟩,⟨sg26868,⟨sg26867,True.intro,True.intro⟩,⟨sg26869,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_250All : degreeTree43_250.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26886,⟨sg26878,⟨sg26874,⟨sg26872,⟨sg26871,True.intro,True.intro⟩,⟨sg26873,True.intro,True.intro⟩⟩,⟨sg26876,⟨sg26875,True.intro,True.intro⟩,⟨sg26877,True.intro,True.intro⟩⟩⟩,⟨sg26882,⟨sg26880,⟨sg26879,True.intro,True.intro⟩,⟨sg26881,True.intro,True.intro⟩⟩,⟨sg26884,⟨sg26883,True.intro,True.intro⟩,⟨sg26885,True.intro,True.intro⟩⟩⟩⟩,⟨sg26894,⟨sg26890,⟨sg26888,⟨sg26887,True.intro,True.intro⟩,⟨sg26889,True.intro,True.intro⟩⟩,⟨sg26892,⟨sg26891,True.intro,True.intro⟩,⟨sg26893,True.intro,True.intro⟩⟩⟩,⟨sg26898,⟨sg26896,⟨sg26895,True.intro,True.intro⟩,⟨sg26897,True.intro,True.intro⟩⟩,⟨sg26900,⟨sg26899,True.intro,True.intro⟩,⟨sg26901,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_251All : degreeTree43_251.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26870,degreeTree43_249All,degreeTree43_250All⟩

lemma degreeTree43_252All : degreeTree43_252.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26838,degreeTree43_248All,degreeTree43_251All⟩

lemma degreeTree43_253All : degreeTree43_253.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26911,⟨sg26907,⟨sg26905,⟨sg26904,⟨sg26903,True.intro,True.intro⟩,True.intro⟩,⟨sg26906,True.intro,True.intro⟩⟩,⟨sg26909,⟨sg26908,True.intro,True.intro⟩,⟨sg26910,True.intro,True.intro⟩⟩⟩,⟨sg26915,⟨sg26913,⟨sg26912,True.intro,True.intro⟩,⟨sg26914,True.intro,True.intro⟩⟩,⟨sg26917,⟨sg26916,True.intro,True.intro⟩,⟨sg26918,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_254All : degreeTree43_254.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26927,⟨sg26923,⟨sg26921,⟨sg26920,True.intro,True.intro⟩,⟨sg26922,True.intro,True.intro⟩⟩,⟨sg26925,⟨sg26924,True.intro,True.intro⟩,⟨sg26926,True.intro,True.intro⟩⟩⟩,⟨sg26931,⟨sg26929,⟨sg26928,True.intro,True.intro⟩,⟨sg26930,True.intro,True.intro⟩⟩,⟨sg26933,⟨sg26932,True.intro,True.intro⟩,⟨sg26934,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_255All : degreeTree43_255.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26919,degreeTree43_253All,degreeTree43_254All⟩

lemma degreeTree43_256All : degreeTree43_256.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26951,⟨sg26943,⟨sg26939,⟨sg26937,⟨sg26936,True.intro,True.intro⟩,⟨sg26938,True.intro,True.intro⟩⟩,⟨sg26941,⟨sg26940,True.intro,True.intro⟩,⟨sg26942,True.intro,True.intro⟩⟩⟩,⟨sg26947,⟨sg26945,⟨sg26944,True.intro,True.intro⟩,⟨sg26946,True.intro,True.intro⟩⟩,⟨sg26949,⟨sg26948,True.intro,True.intro⟩,⟨sg26950,True.intro,True.intro⟩⟩⟩⟩,⟨sg26959,⟨sg26955,⟨sg26953,⟨sg26952,True.intro,True.intro⟩,⟨sg26954,True.intro,True.intro⟩⟩,⟨sg26957,⟨sg26956,True.intro,True.intro⟩,⟨sg26958,True.intro,True.intro⟩⟩⟩,⟨sg26963,⟨sg26961,⟨sg26960,True.intro,True.intro⟩,⟨sg26962,True.intro,True.intro⟩⟩,⟨sg26965,⟨sg26964,True.intro,True.intro⟩,⟨sg26966,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_257All : degreeTree43_257.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26935,degreeTree43_255All,degreeTree43_256All⟩

lemma degreeTree43_258All : degreeTree43_258.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26983,⟨sg26975,⟨sg26971,⟨sg26969,⟨sg26968,True.intro,True.intro⟩,⟨sg26970,True.intro,True.intro⟩⟩,⟨sg26973,⟨sg26972,True.intro,True.intro⟩,⟨sg26974,True.intro,True.intro⟩⟩⟩,⟨sg26979,⟨sg26977,⟨sg26976,True.intro,True.intro⟩,⟨sg26978,True.intro,True.intro⟩⟩,⟨sg26981,⟨sg26980,True.intro,True.intro⟩,⟨sg26982,True.intro,True.intro⟩⟩⟩⟩,⟨sg26991,⟨sg26987,⟨sg26985,⟨sg26984,True.intro,True.intro⟩,⟨sg26986,True.intro,True.intro⟩⟩,⟨sg26989,⟨sg26988,True.intro,True.intro⟩,⟨sg26990,True.intro,True.intro⟩⟩⟩,⟨sg26995,⟨sg26993,⟨sg26992,True.intro,True.intro⟩,⟨sg26994,True.intro,True.intro⟩⟩,⟨sg26997,⟨sg26996,True.intro,True.intro⟩,⟨sg26998,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_259All : degreeTree43_259.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27015,⟨sg27007,⟨sg27003,⟨sg27001,⟨sg27000,True.intro,True.intro⟩,⟨sg27002,True.intro,True.intro⟩⟩,⟨sg27005,⟨sg27004,True.intro,True.intro⟩,⟨sg27006,True.intro,True.intro⟩⟩⟩,⟨sg27011,⟨sg27009,⟨sg27008,True.intro,True.intro⟩,⟨sg27010,True.intro,True.intro⟩⟩,⟨sg27013,⟨sg27012,True.intro,True.intro⟩,⟨sg27014,True.intro,True.intro⟩⟩⟩⟩,⟨sg27023,⟨sg27019,⟨sg27017,⟨sg27016,True.intro,True.intro⟩,⟨sg27018,True.intro,True.intro⟩⟩,⟨sg27021,⟨sg27020,True.intro,True.intro⟩,⟨sg27022,True.intro,True.intro⟩⟩⟩,⟨sg27027,⟨sg27025,⟨sg27024,True.intro,True.intro⟩,⟨sg27026,True.intro,True.intro⟩⟩,⟨sg27029,⟨sg27028,True.intro,True.intro⟩,⟨sg27030,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_260All : degreeTree43_260.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26999,degreeTree43_258All,degreeTree43_259All⟩

lemma degreeTree43_261All : degreeTree43_261.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26967,degreeTree43_257All,degreeTree43_260All⟩

lemma degreeTree43_262All : degreeTree43_262.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26902,degreeTree43_252All,degreeTree43_261All⟩

lemma degreeTree43_263All : degreeTree43_263.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27040,⟨sg27036,⟨sg27034,⟨sg27033,⟨sg27032,True.intro,True.intro⟩,True.intro⟩,⟨sg27035,True.intro,True.intro⟩⟩,⟨sg27038,⟨sg27037,True.intro,True.intro⟩,⟨sg27039,True.intro,True.intro⟩⟩⟩,⟨sg27044,⟨sg27042,⟨sg27041,True.intro,True.intro⟩,⟨sg27043,True.intro,True.intro⟩⟩,⟨sg27046,⟨sg27045,True.intro,True.intro⟩,⟨sg27047,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_264All : degreeTree43_264.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27056,⟨sg27052,⟨sg27050,⟨sg27049,True.intro,True.intro⟩,⟨sg27051,True.intro,True.intro⟩⟩,⟨sg27054,⟨sg27053,True.intro,True.intro⟩,⟨sg27055,True.intro,True.intro⟩⟩⟩,⟨sg27060,⟨sg27058,⟨sg27057,True.intro,True.intro⟩,⟨sg27059,True.intro,True.intro⟩⟩,⟨sg27062,⟨sg27061,True.intro,True.intro⟩,⟨sg27063,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_265All : degreeTree43_265.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27048,degreeTree43_263All,degreeTree43_264All⟩

lemma degreeTree43_266All : degreeTree43_266.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27080,⟨sg27072,⟨sg27068,⟨sg27066,⟨sg27065,True.intro,True.intro⟩,⟨sg27067,True.intro,True.intro⟩⟩,⟨sg27070,⟨sg27069,True.intro,True.intro⟩,⟨sg27071,True.intro,True.intro⟩⟩⟩,⟨sg27076,⟨sg27074,⟨sg27073,True.intro,True.intro⟩,⟨sg27075,True.intro,True.intro⟩⟩,⟨sg27078,⟨sg27077,True.intro,True.intro⟩,⟨sg27079,True.intro,True.intro⟩⟩⟩⟩,⟨sg27088,⟨sg27084,⟨sg27082,⟨sg27081,True.intro,True.intro⟩,⟨sg27083,True.intro,True.intro⟩⟩,⟨sg27086,⟨sg27085,True.intro,True.intro⟩,⟨sg27087,True.intro,True.intro⟩⟩⟩,⟨sg27092,⟨sg27090,⟨sg27089,True.intro,True.intro⟩,⟨sg27091,True.intro,True.intro⟩⟩,⟨sg27094,⟨sg27093,True.intro,True.intro⟩,⟨sg27095,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_267All : degreeTree43_267.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27064,degreeTree43_265All,degreeTree43_266All⟩

lemma degreeTree43_268All : degreeTree43_268.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27112,⟨sg27104,⟨sg27100,⟨sg27098,⟨sg27097,True.intro,True.intro⟩,⟨sg27099,True.intro,True.intro⟩⟩,⟨sg27102,⟨sg27101,True.intro,True.intro⟩,⟨sg27103,True.intro,True.intro⟩⟩⟩,⟨sg27108,⟨sg27106,⟨sg27105,True.intro,True.intro⟩,⟨sg27107,True.intro,True.intro⟩⟩,⟨sg27110,⟨sg27109,True.intro,True.intro⟩,⟨sg27111,True.intro,True.intro⟩⟩⟩⟩,⟨sg27120,⟨sg27116,⟨sg27114,⟨sg27113,True.intro,True.intro⟩,⟨sg27115,True.intro,True.intro⟩⟩,⟨sg27118,⟨sg27117,True.intro,True.intro⟩,⟨sg27119,True.intro,True.intro⟩⟩⟩,⟨sg27124,⟨sg27122,⟨sg27121,True.intro,True.intro⟩,⟨sg27123,True.intro,True.intro⟩⟩,⟨sg27126,⟨sg27125,True.intro,True.intro⟩,⟨sg27127,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_269All : degreeTree43_269.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27144,⟨sg27136,⟨sg27132,⟨sg27130,⟨sg27129,True.intro,True.intro⟩,⟨sg27131,True.intro,True.intro⟩⟩,⟨sg27134,⟨sg27133,True.intro,True.intro⟩,⟨sg27135,True.intro,True.intro⟩⟩⟩,⟨sg27140,⟨sg27138,⟨sg27137,True.intro,True.intro⟩,⟨sg27139,True.intro,True.intro⟩⟩,⟨sg27142,⟨sg27141,True.intro,True.intro⟩,⟨sg27143,True.intro,True.intro⟩⟩⟩⟩,⟨sg27152,⟨sg27148,⟨sg27146,⟨sg27145,True.intro,True.intro⟩,⟨sg27147,True.intro,True.intro⟩⟩,⟨sg27150,⟨sg27149,True.intro,True.intro⟩,⟨sg27151,True.intro,True.intro⟩⟩⟩,⟨sg27156,⟨sg27154,⟨sg27153,True.intro,True.intro⟩,⟨sg27155,True.intro,True.intro⟩⟩,⟨sg27158,⟨sg27157,True.intro,True.intro⟩,⟨sg27159,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_270All : degreeTree43_270.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27128,degreeTree43_268All,degreeTree43_269All⟩

lemma degreeTree43_271All : degreeTree43_271.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27096,degreeTree43_267All,degreeTree43_270All⟩

lemma degreeTree43_272All : degreeTree43_272.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27169,⟨sg27165,⟨sg27163,⟨sg27162,⟨sg27161,True.intro,True.intro⟩,True.intro⟩,⟨sg27164,True.intro,True.intro⟩⟩,⟨sg27167,⟨sg27166,True.intro,True.intro⟩,⟨sg27168,True.intro,True.intro⟩⟩⟩,⟨sg27173,⟨sg27171,⟨sg27170,True.intro,True.intro⟩,⟨sg27172,True.intro,True.intro⟩⟩,⟨sg27175,⟨sg27174,True.intro,True.intro⟩,⟨sg27176,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_273All : degreeTree43_273.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27185,⟨sg27181,⟨sg27179,⟨sg27178,True.intro,True.intro⟩,⟨sg27180,True.intro,True.intro⟩⟩,⟨sg27183,⟨sg27182,True.intro,True.intro⟩,⟨sg27184,True.intro,True.intro⟩⟩⟩,⟨sg27189,⟨sg27187,⟨sg27186,True.intro,True.intro⟩,⟨sg27188,True.intro,True.intro⟩⟩,⟨sg27191,⟨sg27190,True.intro,True.intro⟩,⟨sg27192,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_274All : degreeTree43_274.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27177,degreeTree43_272All,degreeTree43_273All⟩

lemma degreeTree43_275All : degreeTree43_275.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27209,⟨sg27201,⟨sg27197,⟨sg27195,⟨sg27194,True.intro,True.intro⟩,⟨sg27196,True.intro,True.intro⟩⟩,⟨sg27199,⟨sg27198,True.intro,True.intro⟩,⟨sg27200,True.intro,True.intro⟩⟩⟩,⟨sg27205,⟨sg27203,⟨sg27202,True.intro,True.intro⟩,⟨sg27204,True.intro,True.intro⟩⟩,⟨sg27207,⟨sg27206,True.intro,True.intro⟩,⟨sg27208,True.intro,True.intro⟩⟩⟩⟩,⟨sg27217,⟨sg27213,⟨sg27211,⟨sg27210,True.intro,True.intro⟩,⟨sg27212,True.intro,True.intro⟩⟩,⟨sg27215,⟨sg27214,True.intro,True.intro⟩,⟨sg27216,True.intro,True.intro⟩⟩⟩,⟨sg27221,⟨sg27219,⟨sg27218,True.intro,True.intro⟩,⟨sg27220,True.intro,True.intro⟩⟩,⟨sg27223,⟨sg27222,True.intro,True.intro⟩,⟨sg27224,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_276All : degreeTree43_276.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27193,degreeTree43_274All,degreeTree43_275All⟩

lemma degreeTree43_277All : degreeTree43_277.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27241,⟨sg27233,⟨sg27229,⟨sg27227,⟨sg27226,True.intro,True.intro⟩,⟨sg27228,True.intro,True.intro⟩⟩,⟨sg27231,⟨sg27230,True.intro,True.intro⟩,⟨sg27232,True.intro,True.intro⟩⟩⟩,⟨sg27237,⟨sg27235,⟨sg27234,True.intro,True.intro⟩,⟨sg27236,True.intro,True.intro⟩⟩,⟨sg27239,⟨sg27238,True.intro,True.intro⟩,⟨sg27240,True.intro,True.intro⟩⟩⟩⟩,⟨sg27249,⟨sg27245,⟨sg27243,⟨sg27242,True.intro,True.intro⟩,⟨sg27244,True.intro,True.intro⟩⟩,⟨sg27247,⟨sg27246,True.intro,True.intro⟩,⟨sg27248,True.intro,True.intro⟩⟩⟩,⟨sg27253,⟨sg27251,⟨sg27250,True.intro,True.intro⟩,⟨sg27252,True.intro,True.intro⟩⟩,⟨sg27255,⟨sg27254,True.intro,True.intro⟩,⟨sg27256,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_278All : degreeTree43_278.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27273,⟨sg27265,⟨sg27261,⟨sg27259,⟨sg27258,True.intro,True.intro⟩,⟨sg27260,True.intro,True.intro⟩⟩,⟨sg27263,⟨sg27262,True.intro,True.intro⟩,⟨sg27264,True.intro,True.intro⟩⟩⟩,⟨sg27269,⟨sg27267,⟨sg27266,True.intro,True.intro⟩,⟨sg27268,True.intro,True.intro⟩⟩,⟨sg27271,⟨sg27270,True.intro,True.intro⟩,⟨sg27272,True.intro,True.intro⟩⟩⟩⟩,⟨sg27281,⟨sg27277,⟨sg27275,⟨sg27274,True.intro,True.intro⟩,⟨sg27276,True.intro,True.intro⟩⟩,⟨sg27279,⟨sg27278,True.intro,True.intro⟩,⟨sg27280,True.intro,True.intro⟩⟩⟩,⟨sg27285,⟨sg27283,⟨sg27282,True.intro,True.intro⟩,⟨sg27284,True.intro,True.intro⟩⟩,⟨sg27287,⟨sg27286,True.intro,True.intro⟩,⟨sg27288,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_279All : degreeTree43_279.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27257,degreeTree43_277All,degreeTree43_278All⟩

lemma degreeTree43_280All : degreeTree43_280.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27225,degreeTree43_276All,degreeTree43_279All⟩

lemma degreeTree43_281All : degreeTree43_281.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27160,degreeTree43_271All,degreeTree43_280All⟩

lemma degreeTree43_282All : degreeTree43_282.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27031,degreeTree43_262All,degreeTree43_281All⟩

lemma degreeTree43_283All : degreeTree43_283.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27298,⟨sg27294,⟨sg27292,⟨sg27291,⟨sg27290,True.intro,True.intro⟩,True.intro⟩,⟨sg27293,True.intro,True.intro⟩⟩,⟨sg27296,⟨sg27295,True.intro,True.intro⟩,⟨sg27297,True.intro,True.intro⟩⟩⟩,⟨sg27302,⟨sg27300,⟨sg27299,True.intro,True.intro⟩,⟨sg27301,True.intro,True.intro⟩⟩,⟨sg27304,⟨sg27303,True.intro,True.intro⟩,⟨sg27305,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_284All : degreeTree43_284.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27314,⟨sg27310,⟨sg27308,⟨sg27307,True.intro,True.intro⟩,⟨sg27309,True.intro,True.intro⟩⟩,⟨sg27312,⟨sg27311,True.intro,True.intro⟩,⟨sg27313,True.intro,True.intro⟩⟩⟩,⟨sg27318,⟨sg27316,⟨sg27315,True.intro,True.intro⟩,⟨sg27317,True.intro,True.intro⟩⟩,⟨sg27320,⟨sg27319,True.intro,True.intro⟩,⟨sg27321,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_285All : degreeTree43_285.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27306,degreeTree43_283All,degreeTree43_284All⟩

lemma degreeTree43_286All : degreeTree43_286.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27338,⟨sg27330,⟨sg27326,⟨sg27324,⟨sg27323,True.intro,True.intro⟩,⟨sg27325,True.intro,True.intro⟩⟩,⟨sg27328,⟨sg27327,True.intro,True.intro⟩,⟨sg27329,True.intro,True.intro⟩⟩⟩,⟨sg27334,⟨sg27332,⟨sg27331,True.intro,True.intro⟩,⟨sg27333,True.intro,True.intro⟩⟩,⟨sg27336,⟨sg27335,True.intro,True.intro⟩,⟨sg27337,True.intro,True.intro⟩⟩⟩⟩,⟨sg27346,⟨sg27342,⟨sg27340,⟨sg27339,True.intro,True.intro⟩,⟨sg27341,True.intro,True.intro⟩⟩,⟨sg27344,⟨sg27343,True.intro,True.intro⟩,⟨sg27345,True.intro,True.intro⟩⟩⟩,⟨sg27350,⟨sg27348,⟨sg27347,True.intro,True.intro⟩,⟨sg27349,True.intro,True.intro⟩⟩,⟨sg27352,⟨sg27351,True.intro,True.intro⟩,⟨sg27353,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_287All : degreeTree43_287.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27322,degreeTree43_285All,degreeTree43_286All⟩

lemma degreeTree43_288All : degreeTree43_288.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27370,⟨sg27362,⟨sg27358,⟨sg27356,⟨sg27355,True.intro,True.intro⟩,⟨sg27357,True.intro,True.intro⟩⟩,⟨sg27360,⟨sg27359,True.intro,True.intro⟩,⟨sg27361,True.intro,True.intro⟩⟩⟩,⟨sg27366,⟨sg27364,⟨sg27363,True.intro,True.intro⟩,⟨sg27365,True.intro,True.intro⟩⟩,⟨sg27368,⟨sg27367,True.intro,True.intro⟩,⟨sg27369,True.intro,True.intro⟩⟩⟩⟩,⟨sg27378,⟨sg27374,⟨sg27372,⟨sg27371,True.intro,True.intro⟩,⟨sg27373,True.intro,True.intro⟩⟩,⟨sg27376,⟨sg27375,True.intro,True.intro⟩,⟨sg27377,True.intro,True.intro⟩⟩⟩,⟨sg27382,⟨sg27380,⟨sg27379,True.intro,True.intro⟩,⟨sg27381,True.intro,True.intro⟩⟩,⟨sg27384,⟨sg27383,True.intro,True.intro⟩,⟨sg27385,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_289All : degreeTree43_289.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27402,⟨sg27394,⟨sg27390,⟨sg27388,⟨sg27387,True.intro,True.intro⟩,⟨sg27389,True.intro,True.intro⟩⟩,⟨sg27392,⟨sg27391,True.intro,True.intro⟩,⟨sg27393,True.intro,True.intro⟩⟩⟩,⟨sg27398,⟨sg27396,⟨sg27395,True.intro,True.intro⟩,⟨sg27397,True.intro,True.intro⟩⟩,⟨sg27400,⟨sg27399,True.intro,True.intro⟩,⟨sg27401,True.intro,True.intro⟩⟩⟩⟩,⟨sg27410,⟨sg27406,⟨sg27404,⟨sg27403,True.intro,True.intro⟩,⟨sg27405,True.intro,True.intro⟩⟩,⟨sg27408,⟨sg27407,True.intro,True.intro⟩,⟨sg27409,True.intro,True.intro⟩⟩⟩,⟨sg27414,⟨sg27412,⟨sg27411,True.intro,True.intro⟩,⟨sg27413,True.intro,True.intro⟩⟩,⟨sg27416,⟨sg27415,True.intro,True.intro⟩,⟨sg27417,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_290All : degreeTree43_290.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27386,degreeTree43_288All,degreeTree43_289All⟩

lemma degreeTree43_291All : degreeTree43_291.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27354,degreeTree43_287All,degreeTree43_290All⟩

lemma degreeTree43_292All : degreeTree43_292.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27427,⟨sg27423,⟨sg27421,⟨sg27420,⟨sg27419,True.intro,True.intro⟩,True.intro⟩,⟨sg27422,True.intro,True.intro⟩⟩,⟨sg27425,⟨sg27424,True.intro,True.intro⟩,⟨sg27426,True.intro,True.intro⟩⟩⟩,⟨sg27431,⟨sg27429,⟨sg27428,True.intro,True.intro⟩,⟨sg27430,True.intro,True.intro⟩⟩,⟨sg27433,⟨sg27432,True.intro,True.intro⟩,⟨sg27434,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_293All : degreeTree43_293.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27443,⟨sg27439,⟨sg27437,⟨sg27436,True.intro,True.intro⟩,⟨sg27438,True.intro,True.intro⟩⟩,⟨sg27441,⟨sg27440,True.intro,True.intro⟩,⟨sg27442,True.intro,True.intro⟩⟩⟩,⟨sg27447,⟨sg27445,⟨sg27444,True.intro,True.intro⟩,⟨sg27446,True.intro,True.intro⟩⟩,⟨sg27449,⟨sg27448,True.intro,True.intro⟩,⟨sg27450,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_294All : degreeTree43_294.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27435,degreeTree43_292All,degreeTree43_293All⟩

lemma degreeTree43_295All : degreeTree43_295.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27467,⟨sg27459,⟨sg27455,⟨sg27453,⟨sg27452,True.intro,True.intro⟩,⟨sg27454,True.intro,True.intro⟩⟩,⟨sg27457,⟨sg27456,True.intro,True.intro⟩,⟨sg27458,True.intro,True.intro⟩⟩⟩,⟨sg27463,⟨sg27461,⟨sg27460,True.intro,True.intro⟩,⟨sg27462,True.intro,True.intro⟩⟩,⟨sg27465,⟨sg27464,True.intro,True.intro⟩,⟨sg27466,True.intro,True.intro⟩⟩⟩⟩,⟨sg27475,⟨sg27471,⟨sg27469,⟨sg27468,True.intro,True.intro⟩,⟨sg27470,True.intro,True.intro⟩⟩,⟨sg27473,⟨sg27472,True.intro,True.intro⟩,⟨sg27474,True.intro,True.intro⟩⟩⟩,⟨sg27479,⟨sg27477,⟨sg27476,True.intro,True.intro⟩,⟨sg27478,True.intro,True.intro⟩⟩,⟨sg27481,⟨sg27480,True.intro,True.intro⟩,⟨sg27482,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_296All : degreeTree43_296.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27451,degreeTree43_294All,degreeTree43_295All⟩

lemma degreeTree43_297All : degreeTree43_297.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27499,⟨sg27491,⟨sg27487,⟨sg27485,⟨sg27484,True.intro,True.intro⟩,⟨sg27486,True.intro,True.intro⟩⟩,⟨sg27489,⟨sg27488,True.intro,True.intro⟩,⟨sg27490,True.intro,True.intro⟩⟩⟩,⟨sg27495,⟨sg27493,⟨sg27492,True.intro,True.intro⟩,⟨sg27494,True.intro,True.intro⟩⟩,⟨sg27497,⟨sg27496,True.intro,True.intro⟩,⟨sg27498,True.intro,True.intro⟩⟩⟩⟩,⟨sg27507,⟨sg27503,⟨sg27501,⟨sg27500,True.intro,True.intro⟩,⟨sg27502,True.intro,True.intro⟩⟩,⟨sg27505,⟨sg27504,True.intro,True.intro⟩,⟨sg27506,True.intro,True.intro⟩⟩⟩,⟨sg27511,⟨sg27509,⟨sg27508,True.intro,True.intro⟩,⟨sg27510,True.intro,True.intro⟩⟩,⟨sg27513,⟨sg27512,True.intro,True.intro⟩,⟨sg27514,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_298All : degreeTree43_298.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27531,⟨sg27523,⟨sg27519,⟨sg27517,⟨sg27516,True.intro,True.intro⟩,⟨sg27518,True.intro,True.intro⟩⟩,⟨sg27521,⟨sg27520,True.intro,True.intro⟩,⟨sg27522,True.intro,True.intro⟩⟩⟩,⟨sg27527,⟨sg27525,⟨sg27524,True.intro,True.intro⟩,⟨sg27526,True.intro,True.intro⟩⟩,⟨sg27529,⟨sg27528,True.intro,True.intro⟩,⟨sg27530,True.intro,True.intro⟩⟩⟩⟩,⟨sg27539,⟨sg27535,⟨sg27533,⟨sg27532,True.intro,True.intro⟩,⟨sg27534,True.intro,True.intro⟩⟩,⟨sg27537,⟨sg27536,True.intro,True.intro⟩,⟨sg27538,True.intro,True.intro⟩⟩⟩,⟨sg27543,⟨sg27541,⟨sg27540,True.intro,True.intro⟩,⟨sg27542,True.intro,True.intro⟩⟩,⟨sg27545,⟨sg27544,True.intro,True.intro⟩,⟨sg27546,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_299All : degreeTree43_299.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27515,degreeTree43_297All,degreeTree43_298All⟩

lemma degreeTree43_300All : degreeTree43_300.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27483,degreeTree43_296All,degreeTree43_299All⟩

lemma degreeTree43_301All : degreeTree43_301.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27418,degreeTree43_291All,degreeTree43_300All⟩

lemma degreeTree43_302All : degreeTree43_302.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27556,⟨sg27552,⟨sg27550,⟨sg27549,⟨sg27548,True.intro,True.intro⟩,True.intro⟩,⟨sg27551,True.intro,True.intro⟩⟩,⟨sg27554,⟨sg27553,True.intro,True.intro⟩,⟨sg27555,True.intro,True.intro⟩⟩⟩,⟨sg27560,⟨sg27558,⟨sg27557,True.intro,True.intro⟩,⟨sg27559,True.intro,True.intro⟩⟩,⟨sg27562,⟨sg27561,True.intro,True.intro⟩,⟨sg27563,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_303All : degreeTree43_303.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27572,⟨sg27568,⟨sg27566,⟨sg27565,True.intro,True.intro⟩,⟨sg27567,True.intro,True.intro⟩⟩,⟨sg27570,⟨sg27569,True.intro,True.intro⟩,⟨sg27571,True.intro,True.intro⟩⟩⟩,⟨sg27576,⟨sg27574,⟨sg27573,True.intro,True.intro⟩,⟨sg27575,True.intro,True.intro⟩⟩,⟨sg27578,⟨sg27577,True.intro,True.intro⟩,⟨sg27579,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_304All : degreeTree43_304.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27564,degreeTree43_302All,degreeTree43_303All⟩

lemma degreeTree43_305All : degreeTree43_305.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27596,⟨sg27588,⟨sg27584,⟨sg27582,⟨sg27581,True.intro,True.intro⟩,⟨sg27583,True.intro,True.intro⟩⟩,⟨sg27586,⟨sg27585,True.intro,True.intro⟩,⟨sg27587,True.intro,True.intro⟩⟩⟩,⟨sg27592,⟨sg27590,⟨sg27589,True.intro,True.intro⟩,⟨sg27591,True.intro,True.intro⟩⟩,⟨sg27594,⟨sg27593,True.intro,True.intro⟩,⟨sg27595,True.intro,True.intro⟩⟩⟩⟩,⟨sg27604,⟨sg27600,⟨sg27598,⟨sg27597,True.intro,True.intro⟩,⟨sg27599,True.intro,True.intro⟩⟩,⟨sg27602,⟨sg27601,True.intro,True.intro⟩,⟨sg27603,True.intro,True.intro⟩⟩⟩,⟨sg27608,⟨sg27606,⟨sg27605,True.intro,True.intro⟩,⟨sg27607,True.intro,True.intro⟩⟩,⟨sg27610,⟨sg27609,True.intro,True.intro⟩,⟨sg27611,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_306All : degreeTree43_306.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27580,degreeTree43_304All,degreeTree43_305All⟩

lemma degreeTree43_307All : degreeTree43_307.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27628,⟨sg27620,⟨sg27616,⟨sg27614,⟨sg27613,True.intro,True.intro⟩,⟨sg27615,True.intro,True.intro⟩⟩,⟨sg27618,⟨sg27617,True.intro,True.intro⟩,⟨sg27619,True.intro,True.intro⟩⟩⟩,⟨sg27624,⟨sg27622,⟨sg27621,True.intro,True.intro⟩,⟨sg27623,True.intro,True.intro⟩⟩,⟨sg27626,⟨sg27625,True.intro,True.intro⟩,⟨sg27627,True.intro,True.intro⟩⟩⟩⟩,⟨sg27636,⟨sg27632,⟨sg27630,⟨sg27629,True.intro,True.intro⟩,⟨sg27631,True.intro,True.intro⟩⟩,⟨sg27634,⟨sg27633,True.intro,True.intro⟩,⟨sg27635,True.intro,True.intro⟩⟩⟩,⟨sg27640,⟨sg27638,⟨sg27637,True.intro,True.intro⟩,⟨sg27639,True.intro,True.intro⟩⟩,⟨sg27642,⟨sg27641,True.intro,True.intro⟩,⟨sg27643,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_308All : degreeTree43_308.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27660,⟨sg27652,⟨sg27648,⟨sg27646,⟨sg27645,True.intro,True.intro⟩,⟨sg27647,True.intro,True.intro⟩⟩,⟨sg27650,⟨sg27649,True.intro,True.intro⟩,⟨sg27651,True.intro,True.intro⟩⟩⟩,⟨sg27656,⟨sg27654,⟨sg27653,True.intro,True.intro⟩,⟨sg27655,True.intro,True.intro⟩⟩,⟨sg27658,⟨sg27657,True.intro,True.intro⟩,⟨sg27659,True.intro,True.intro⟩⟩⟩⟩,⟨sg27668,⟨sg27664,⟨sg27662,⟨sg27661,True.intro,True.intro⟩,⟨sg27663,True.intro,True.intro⟩⟩,⟨sg27666,⟨sg27665,True.intro,True.intro⟩,⟨sg27667,True.intro,True.intro⟩⟩⟩,⟨sg27672,⟨sg27670,⟨sg27669,True.intro,True.intro⟩,⟨sg27671,True.intro,True.intro⟩⟩,⟨sg27674,⟨sg27673,True.intro,True.intro⟩,⟨sg27675,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_309All : degreeTree43_309.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27644,degreeTree43_307All,degreeTree43_308All⟩

lemma degreeTree43_310All : degreeTree43_310.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27612,degreeTree43_306All,degreeTree43_309All⟩

lemma degreeTree43_311All : degreeTree43_311.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27685,⟨sg27681,⟨sg27679,⟨sg27678,⟨sg27677,True.intro,True.intro⟩,True.intro⟩,⟨sg27680,True.intro,True.intro⟩⟩,⟨sg27683,⟨sg27682,True.intro,True.intro⟩,⟨sg27684,True.intro,True.intro⟩⟩⟩,⟨sg27689,⟨sg27687,⟨sg27686,True.intro,True.intro⟩,⟨sg27688,True.intro,True.intro⟩⟩,⟨sg27691,⟨sg27690,True.intro,True.intro⟩,⟨sg27692,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_312All : degreeTree43_312.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27701,⟨sg27697,⟨sg27695,⟨sg27694,True.intro,True.intro⟩,⟨sg27696,True.intro,True.intro⟩⟩,⟨sg27699,⟨sg27698,True.intro,True.intro⟩,⟨sg27700,True.intro,True.intro⟩⟩⟩,⟨sg27705,⟨sg27703,⟨sg27702,True.intro,True.intro⟩,⟨sg27704,True.intro,True.intro⟩⟩,⟨sg27707,⟨sg27706,True.intro,True.intro⟩,⟨sg27708,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_313All : degreeTree43_313.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27693,degreeTree43_311All,degreeTree43_312All⟩

lemma degreeTree43_314All : degreeTree43_314.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27725,⟨sg27717,⟨sg27713,⟨sg27711,⟨sg27710,True.intro,True.intro⟩,⟨sg27712,True.intro,True.intro⟩⟩,⟨sg27715,⟨sg27714,True.intro,True.intro⟩,⟨sg27716,True.intro,True.intro⟩⟩⟩,⟨sg27721,⟨sg27719,⟨sg27718,True.intro,True.intro⟩,⟨sg27720,True.intro,True.intro⟩⟩,⟨sg27723,⟨sg27722,True.intro,True.intro⟩,⟨sg27724,True.intro,True.intro⟩⟩⟩⟩,⟨sg27733,⟨sg27729,⟨sg27727,⟨sg27726,True.intro,True.intro⟩,⟨sg27728,True.intro,True.intro⟩⟩,⟨sg27731,⟨sg27730,True.intro,True.intro⟩,⟨sg27732,True.intro,True.intro⟩⟩⟩,⟨sg27737,⟨sg27735,⟨sg27734,True.intro,True.intro⟩,⟨sg27736,True.intro,True.intro⟩⟩,⟨sg27739,⟨sg27738,True.intro,True.intro⟩,⟨sg27740,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_315All : degreeTree43_315.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27709,degreeTree43_313All,degreeTree43_314All⟩

lemma degreeTree43_316All : degreeTree43_316.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27757,⟨sg27749,⟨sg27745,⟨sg27743,⟨sg27742,True.intro,True.intro⟩,⟨sg27744,True.intro,True.intro⟩⟩,⟨sg27747,⟨sg27746,True.intro,True.intro⟩,⟨sg27748,True.intro,True.intro⟩⟩⟩,⟨sg27753,⟨sg27751,⟨sg27750,True.intro,True.intro⟩,⟨sg27752,True.intro,True.intro⟩⟩,⟨sg27755,⟨sg27754,True.intro,True.intro⟩,⟨sg27756,True.intro,True.intro⟩⟩⟩⟩,⟨sg27765,⟨sg27761,⟨sg27759,⟨sg27758,True.intro,True.intro⟩,⟨sg27760,True.intro,True.intro⟩⟩,⟨sg27763,⟨sg27762,True.intro,True.intro⟩,⟨sg27764,True.intro,True.intro⟩⟩⟩,⟨sg27769,⟨sg27767,⟨sg27766,True.intro,True.intro⟩,⟨sg27768,True.intro,True.intro⟩⟩,⟨sg27771,⟨sg27770,True.intro,True.intro⟩,⟨sg27772,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_317All : degreeTree43_317.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27789,⟨sg27781,⟨sg27777,⟨sg27775,⟨sg27774,True.intro,True.intro⟩,⟨sg27776,True.intro,True.intro⟩⟩,⟨sg27779,⟨sg27778,True.intro,True.intro⟩,⟨sg27780,True.intro,True.intro⟩⟩⟩,⟨sg27785,⟨sg27783,⟨sg27782,True.intro,True.intro⟩,⟨sg27784,True.intro,True.intro⟩⟩,⟨sg27787,⟨sg27786,True.intro,True.intro⟩,⟨sg27788,True.intro,True.intro⟩⟩⟩⟩,⟨sg27797,⟨sg27793,⟨sg27791,⟨sg27790,True.intro,True.intro⟩,⟨sg27792,True.intro,True.intro⟩⟩,⟨sg27795,⟨sg27794,True.intro,True.intro⟩,⟨sg27796,True.intro,True.intro⟩⟩⟩,⟨sg27801,⟨sg27799,⟨sg27798,True.intro,True.intro⟩,⟨sg27800,True.intro,True.intro⟩⟩,⟨sg27803,⟨sg27802,True.intro,True.intro⟩,⟨sg27804,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_318All : degreeTree43_318.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27773,degreeTree43_316All,degreeTree43_317All⟩

lemma degreeTree43_319All : degreeTree43_319.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27741,degreeTree43_315All,degreeTree43_318All⟩

lemma degreeTree43_320All : degreeTree43_320.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27676,degreeTree43_310All,degreeTree43_319All⟩

lemma degreeTree43_321All : degreeTree43_321.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27547,degreeTree43_301All,degreeTree43_320All⟩

lemma degreeTree43_322All : degreeTree43_322.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27289,degreeTree43_282All,degreeTree43_321All⟩

lemma degreeTree43_323All : degreeTree43_323.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg26773,degreeTree43_243All,degreeTree43_322All⟩

lemma degreeTree43_324All : degreeTree43_324.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg25740,degreeTree43_162All,degreeTree43_323All⟩

lemma degreeTree43_325All : degreeTree43_325.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27814,⟨sg27810,⟨sg27808,⟨sg27807,⟨sg27806,True.intro,True.intro⟩,True.intro⟩,⟨sg27809,True.intro,True.intro⟩⟩,⟨sg27812,⟨sg27811,True.intro,True.intro⟩,⟨sg27813,True.intro,True.intro⟩⟩⟩,⟨sg27818,⟨sg27816,⟨sg27815,True.intro,True.intro⟩,⟨sg27817,True.intro,True.intro⟩⟩,⟨sg27820,⟨sg27819,True.intro,True.intro⟩,⟨sg27821,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_326All : degreeTree43_326.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27830,⟨sg27826,⟨sg27824,⟨sg27823,True.intro,True.intro⟩,⟨sg27825,True.intro,True.intro⟩⟩,⟨sg27828,⟨sg27827,True.intro,True.intro⟩,⟨sg27829,True.intro,True.intro⟩⟩⟩,⟨sg27834,⟨sg27832,⟨sg27831,True.intro,True.intro⟩,⟨sg27833,True.intro,True.intro⟩⟩,⟨sg27836,⟨sg27835,True.intro,True.intro⟩,⟨sg27837,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_327All : degreeTree43_327.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27822,degreeTree43_325All,degreeTree43_326All⟩

lemma degreeTree43_328All : degreeTree43_328.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27854,⟨sg27846,⟨sg27842,⟨sg27840,⟨sg27839,True.intro,True.intro⟩,⟨sg27841,True.intro,True.intro⟩⟩,⟨sg27844,⟨sg27843,True.intro,True.intro⟩,⟨sg27845,True.intro,True.intro⟩⟩⟩,⟨sg27850,⟨sg27848,⟨sg27847,True.intro,True.intro⟩,⟨sg27849,True.intro,True.intro⟩⟩,⟨sg27852,⟨sg27851,True.intro,True.intro⟩,⟨sg27853,True.intro,True.intro⟩⟩⟩⟩,⟨sg27862,⟨sg27858,⟨sg27856,⟨sg27855,True.intro,True.intro⟩,⟨sg27857,True.intro,True.intro⟩⟩,⟨sg27860,⟨sg27859,True.intro,True.intro⟩,⟨sg27861,True.intro,True.intro⟩⟩⟩,⟨sg27866,⟨sg27864,⟨sg27863,True.intro,True.intro⟩,⟨sg27865,True.intro,True.intro⟩⟩,⟨sg27868,⟨sg27867,True.intro,True.intro⟩,⟨sg27869,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_329All : degreeTree43_329.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27838,degreeTree43_327All,degreeTree43_328All⟩

lemma degreeTree43_330All : degreeTree43_330.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27879,⟨sg27875,⟨sg27873,⟨sg27872,⟨sg27871,True.intro,True.intro⟩,True.intro⟩,⟨sg27874,True.intro,True.intro⟩⟩,⟨sg27877,⟨sg27876,True.intro,True.intro⟩,⟨sg27878,True.intro,True.intro⟩⟩⟩,⟨sg27883,⟨sg27881,⟨sg27880,True.intro,True.intro⟩,⟨sg27882,True.intro,True.intro⟩⟩,⟨sg27885,⟨sg27884,True.intro,True.intro⟩,⟨sg27886,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_331All : degreeTree43_331.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27895,⟨sg27891,⟨sg27889,⟨sg27888,True.intro,True.intro⟩,⟨sg27890,True.intro,True.intro⟩⟩,⟨sg27893,⟨sg27892,True.intro,True.intro⟩,⟨sg27894,True.intro,True.intro⟩⟩⟩,⟨sg27899,⟨sg27897,⟨sg27896,True.intro,True.intro⟩,⟨sg27898,True.intro,True.intro⟩⟩,⟨sg27901,⟨sg27900,True.intro,True.intro⟩,⟨sg27902,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_332All : degreeTree43_332.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27887,degreeTree43_330All,degreeTree43_331All⟩

lemma degreeTree43_333All : degreeTree43_333.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27919,⟨sg27911,⟨sg27907,⟨sg27905,⟨sg27904,True.intro,True.intro⟩,⟨sg27906,True.intro,True.intro⟩⟩,⟨sg27909,⟨sg27908,True.intro,True.intro⟩,⟨sg27910,True.intro,True.intro⟩⟩⟩,⟨sg27915,⟨sg27913,⟨sg27912,True.intro,True.intro⟩,⟨sg27914,True.intro,True.intro⟩⟩,⟨sg27917,⟨sg27916,True.intro,True.intro⟩,⟨sg27918,True.intro,True.intro⟩⟩⟩⟩,⟨sg27927,⟨sg27923,⟨sg27921,⟨sg27920,True.intro,True.intro⟩,⟨sg27922,True.intro,True.intro⟩⟩,⟨sg27925,⟨sg27924,True.intro,True.intro⟩,⟨sg27926,True.intro,True.intro⟩⟩⟩,⟨sg27931,⟨sg27929,⟨sg27928,True.intro,True.intro⟩,⟨sg27930,True.intro,True.intro⟩⟩,⟨sg27933,⟨sg27932,True.intro,True.intro⟩,⟨sg27934,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_334All : degreeTree43_334.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27903,degreeTree43_332All,degreeTree43_333All⟩

lemma degreeTree43_335All : degreeTree43_335.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27870,degreeTree43_329All,degreeTree43_334All⟩

lemma degreeTree43_336All : degreeTree43_336.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27944,⟨sg27940,⟨sg27938,⟨sg27937,⟨sg27936,True.intro,True.intro⟩,True.intro⟩,⟨sg27939,True.intro,True.intro⟩⟩,⟨sg27942,⟨sg27941,True.intro,True.intro⟩,⟨sg27943,True.intro,True.intro⟩⟩⟩,⟨sg27948,⟨sg27946,⟨sg27945,True.intro,True.intro⟩,⟨sg27947,True.intro,True.intro⟩⟩,⟨sg27950,⟨sg27949,True.intro,True.intro⟩,⟨sg27951,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_337All : degreeTree43_337.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27960,⟨sg27956,⟨sg27954,⟨sg27953,True.intro,True.intro⟩,⟨sg27955,True.intro,True.intro⟩⟩,⟨sg27958,⟨sg27957,True.intro,True.intro⟩,⟨sg27959,True.intro,True.intro⟩⟩⟩,⟨sg27964,⟨sg27962,⟨sg27961,True.intro,True.intro⟩,⟨sg27963,True.intro,True.intro⟩⟩,⟨sg27966,⟨sg27965,True.intro,True.intro⟩,⟨sg27967,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_338All : degreeTree43_338.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27952,degreeTree43_336All,degreeTree43_337All⟩

lemma degreeTree43_339All : degreeTree43_339.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27984,⟨sg27976,⟨sg27972,⟨sg27970,⟨sg27969,True.intro,True.intro⟩,⟨sg27971,True.intro,True.intro⟩⟩,⟨sg27974,⟨sg27973,True.intro,True.intro⟩,⟨sg27975,True.intro,True.intro⟩⟩⟩,⟨sg27980,⟨sg27978,⟨sg27977,True.intro,True.intro⟩,⟨sg27979,True.intro,True.intro⟩⟩,⟨sg27982,⟨sg27981,True.intro,True.intro⟩,⟨sg27983,True.intro,True.intro⟩⟩⟩⟩,⟨sg27992,⟨sg27988,⟨sg27986,⟨sg27985,True.intro,True.intro⟩,⟨sg27987,True.intro,True.intro⟩⟩,⟨sg27990,⟨sg27989,True.intro,True.intro⟩,⟨sg27991,True.intro,True.intro⟩⟩⟩,⟨sg27996,⟨sg27994,⟨sg27993,True.intro,True.intro⟩,⟨sg27995,True.intro,True.intro⟩⟩,⟨sg27998,⟨sg27997,True.intro,True.intro⟩,⟨sg27999,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_340All : degreeTree43_340.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27968,degreeTree43_338All,degreeTree43_339All⟩

lemma degreeTree43_341All : degreeTree43_341.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28016,⟨sg28008,⟨sg28004,⟨sg28002,⟨sg28001,True.intro,True.intro⟩,⟨sg28003,True.intro,True.intro⟩⟩,⟨sg28006,⟨sg28005,True.intro,True.intro⟩,⟨sg28007,True.intro,True.intro⟩⟩⟩,⟨sg28012,⟨sg28010,⟨sg28009,True.intro,True.intro⟩,⟨sg28011,True.intro,True.intro⟩⟩,⟨sg28014,⟨sg28013,True.intro,True.intro⟩,⟨sg28015,True.intro,True.intro⟩⟩⟩⟩,⟨sg28024,⟨sg28020,⟨sg28018,⟨sg28017,True.intro,True.intro⟩,⟨sg28019,True.intro,True.intro⟩⟩,⟨sg28022,⟨sg28021,True.intro,True.intro⟩,⟨sg28023,True.intro,True.intro⟩⟩⟩,⟨sg28028,⟨sg28026,⟨sg28025,True.intro,True.intro⟩,⟨sg28027,True.intro,True.intro⟩⟩,⟨sg28030,⟨sg28029,True.intro,True.intro⟩,⟨sg28031,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_342All : degreeTree43_342.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28048,⟨sg28040,⟨sg28036,⟨sg28034,⟨sg28033,True.intro,True.intro⟩,⟨sg28035,True.intro,True.intro⟩⟩,⟨sg28038,⟨sg28037,True.intro,True.intro⟩,⟨sg28039,True.intro,True.intro⟩⟩⟩,⟨sg28044,⟨sg28042,⟨sg28041,True.intro,True.intro⟩,⟨sg28043,True.intro,True.intro⟩⟩,⟨sg28046,⟨sg28045,True.intro,True.intro⟩,⟨sg28047,True.intro,True.intro⟩⟩⟩⟩,⟨sg28056,⟨sg28052,⟨sg28050,⟨sg28049,True.intro,True.intro⟩,⟨sg28051,True.intro,True.intro⟩⟩,⟨sg28054,⟨sg28053,True.intro,True.intro⟩,⟨sg28055,True.intro,True.intro⟩⟩⟩,⟨sg28060,⟨sg28058,⟨sg28057,True.intro,True.intro⟩,⟨sg28059,True.intro,True.intro⟩⟩,⟨sg28062,⟨sg28061,True.intro,True.intro⟩,⟨sg28063,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_343All : degreeTree43_343.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28032,degreeTree43_341All,degreeTree43_342All⟩

lemma degreeTree43_344All : degreeTree43_344.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28000,degreeTree43_340All,degreeTree43_343All⟩

lemma degreeTree43_345All : degreeTree43_345.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27935,degreeTree43_335All,degreeTree43_344All⟩

lemma degreeTree43_346All : degreeTree43_346.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28073,⟨sg28069,⟨sg28067,⟨sg28066,⟨sg28065,True.intro,True.intro⟩,True.intro⟩,⟨sg28068,True.intro,True.intro⟩⟩,⟨sg28071,⟨sg28070,True.intro,True.intro⟩,⟨sg28072,True.intro,True.intro⟩⟩⟩,⟨sg28077,⟨sg28075,⟨sg28074,True.intro,True.intro⟩,⟨sg28076,True.intro,True.intro⟩⟩,⟨sg28079,⟨sg28078,True.intro,True.intro⟩,⟨sg28080,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_347All : degreeTree43_347.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28089,⟨sg28085,⟨sg28083,⟨sg28082,True.intro,True.intro⟩,⟨sg28084,True.intro,True.intro⟩⟩,⟨sg28087,⟨sg28086,True.intro,True.intro⟩,⟨sg28088,True.intro,True.intro⟩⟩⟩,⟨sg28093,⟨sg28091,⟨sg28090,True.intro,True.intro⟩,⟨sg28092,True.intro,True.intro⟩⟩,⟨sg28095,⟨sg28094,True.intro,True.intro⟩,⟨sg28096,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_348All : degreeTree43_348.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28081,degreeTree43_346All,degreeTree43_347All⟩

lemma degreeTree43_349All : degreeTree43_349.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28113,⟨sg28105,⟨sg28101,⟨sg28099,⟨sg28098,True.intro,True.intro⟩,⟨sg28100,True.intro,True.intro⟩⟩,⟨sg28103,⟨sg28102,True.intro,True.intro⟩,⟨sg28104,True.intro,True.intro⟩⟩⟩,⟨sg28109,⟨sg28107,⟨sg28106,True.intro,True.intro⟩,⟨sg28108,True.intro,True.intro⟩⟩,⟨sg28111,⟨sg28110,True.intro,True.intro⟩,⟨sg28112,True.intro,True.intro⟩⟩⟩⟩,⟨sg28121,⟨sg28117,⟨sg28115,⟨sg28114,True.intro,True.intro⟩,⟨sg28116,True.intro,True.intro⟩⟩,⟨sg28119,⟨sg28118,True.intro,True.intro⟩,⟨sg28120,True.intro,True.intro⟩⟩⟩,⟨sg28125,⟨sg28123,⟨sg28122,True.intro,True.intro⟩,⟨sg28124,True.intro,True.intro⟩⟩,⟨sg28127,⟨sg28126,True.intro,True.intro⟩,⟨sg28128,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_350All : degreeTree43_350.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28097,degreeTree43_348All,degreeTree43_349All⟩

lemma degreeTree43_351All : degreeTree43_351.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28145,⟨sg28137,⟨sg28133,⟨sg28131,⟨sg28130,True.intro,True.intro⟩,⟨sg28132,True.intro,True.intro⟩⟩,⟨sg28135,⟨sg28134,True.intro,True.intro⟩,⟨sg28136,True.intro,True.intro⟩⟩⟩,⟨sg28141,⟨sg28139,⟨sg28138,True.intro,True.intro⟩,⟨sg28140,True.intro,True.intro⟩⟩,⟨sg28143,⟨sg28142,True.intro,True.intro⟩,⟨sg28144,True.intro,True.intro⟩⟩⟩⟩,⟨sg28153,⟨sg28149,⟨sg28147,⟨sg28146,True.intro,True.intro⟩,⟨sg28148,True.intro,True.intro⟩⟩,⟨sg28151,⟨sg28150,True.intro,True.intro⟩,⟨sg28152,True.intro,True.intro⟩⟩⟩,⟨sg28157,⟨sg28155,⟨sg28154,True.intro,True.intro⟩,⟨sg28156,True.intro,True.intro⟩⟩,⟨sg28159,⟨sg28158,True.intro,True.intro⟩,⟨sg28160,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_352All : degreeTree43_352.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28177,⟨sg28169,⟨sg28165,⟨sg28163,⟨sg28162,True.intro,True.intro⟩,⟨sg28164,True.intro,True.intro⟩⟩,⟨sg28167,⟨sg28166,True.intro,True.intro⟩,⟨sg28168,True.intro,True.intro⟩⟩⟩,⟨sg28173,⟨sg28171,⟨sg28170,True.intro,True.intro⟩,⟨sg28172,True.intro,True.intro⟩⟩,⟨sg28175,⟨sg28174,True.intro,True.intro⟩,⟨sg28176,True.intro,True.intro⟩⟩⟩⟩,⟨sg28185,⟨sg28181,⟨sg28179,⟨sg28178,True.intro,True.intro⟩,⟨sg28180,True.intro,True.intro⟩⟩,⟨sg28183,⟨sg28182,True.intro,True.intro⟩,⟨sg28184,True.intro,True.intro⟩⟩⟩,⟨sg28189,⟨sg28187,⟨sg28186,True.intro,True.intro⟩,⟨sg28188,True.intro,True.intro⟩⟩,⟨sg28191,⟨sg28190,True.intro,True.intro⟩,⟨sg28192,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_353All : degreeTree43_353.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28161,degreeTree43_351All,degreeTree43_352All⟩

lemma degreeTree43_354All : degreeTree43_354.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28129,degreeTree43_350All,degreeTree43_353All⟩

lemma degreeTree43_355All : degreeTree43_355.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28202,⟨sg28198,⟨sg28196,⟨sg28195,⟨sg28194,True.intro,True.intro⟩,True.intro⟩,⟨sg28197,True.intro,True.intro⟩⟩,⟨sg28200,⟨sg28199,True.intro,True.intro⟩,⟨sg28201,True.intro,True.intro⟩⟩⟩,⟨sg28206,⟨sg28204,⟨sg28203,True.intro,True.intro⟩,⟨sg28205,True.intro,True.intro⟩⟩,⟨sg28208,⟨sg28207,True.intro,True.intro⟩,⟨sg28209,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_356All : degreeTree43_356.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28218,⟨sg28214,⟨sg28212,⟨sg28211,True.intro,True.intro⟩,⟨sg28213,True.intro,True.intro⟩⟩,⟨sg28216,⟨sg28215,True.intro,True.intro⟩,⟨sg28217,True.intro,True.intro⟩⟩⟩,⟨sg28222,⟨sg28220,⟨sg28219,True.intro,True.intro⟩,⟨sg28221,True.intro,True.intro⟩⟩,⟨sg28224,⟨sg28223,True.intro,True.intro⟩,⟨sg28225,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_357All : degreeTree43_357.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28210,degreeTree43_355All,degreeTree43_356All⟩

lemma degreeTree43_358All : degreeTree43_358.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28242,⟨sg28234,⟨sg28230,⟨sg28228,⟨sg28227,True.intro,True.intro⟩,⟨sg28229,True.intro,True.intro⟩⟩,⟨sg28232,⟨sg28231,True.intro,True.intro⟩,⟨sg28233,True.intro,True.intro⟩⟩⟩,⟨sg28238,⟨sg28236,⟨sg28235,True.intro,True.intro⟩,⟨sg28237,True.intro,True.intro⟩⟩,⟨sg28240,⟨sg28239,True.intro,True.intro⟩,⟨sg28241,True.intro,True.intro⟩⟩⟩⟩,⟨sg28250,⟨sg28246,⟨sg28244,⟨sg28243,True.intro,True.intro⟩,⟨sg28245,True.intro,True.intro⟩⟩,⟨sg28248,⟨sg28247,True.intro,True.intro⟩,⟨sg28249,True.intro,True.intro⟩⟩⟩,⟨sg28254,⟨sg28252,⟨sg28251,True.intro,True.intro⟩,⟨sg28253,True.intro,True.intro⟩⟩,⟨sg28256,⟨sg28255,True.intro,True.intro⟩,⟨sg28257,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_359All : degreeTree43_359.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28226,degreeTree43_357All,degreeTree43_358All⟩

lemma degreeTree43_360All : degreeTree43_360.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28274,⟨sg28266,⟨sg28262,⟨sg28260,⟨sg28259,True.intro,True.intro⟩,⟨sg28261,True.intro,True.intro⟩⟩,⟨sg28264,⟨sg28263,True.intro,True.intro⟩,⟨sg28265,True.intro,True.intro⟩⟩⟩,⟨sg28270,⟨sg28268,⟨sg28267,True.intro,True.intro⟩,⟨sg28269,True.intro,True.intro⟩⟩,⟨sg28272,⟨sg28271,True.intro,True.intro⟩,⟨sg28273,True.intro,True.intro⟩⟩⟩⟩,⟨sg28282,⟨sg28278,⟨sg28276,⟨sg28275,True.intro,True.intro⟩,⟨sg28277,True.intro,True.intro⟩⟩,⟨sg28280,⟨sg28279,True.intro,True.intro⟩,⟨sg28281,True.intro,True.intro⟩⟩⟩,⟨sg28286,⟨sg28284,⟨sg28283,True.intro,True.intro⟩,⟨sg28285,True.intro,True.intro⟩⟩,⟨sg28288,⟨sg28287,True.intro,True.intro⟩,⟨sg28289,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_361All : degreeTree43_361.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28306,⟨sg28298,⟨sg28294,⟨sg28292,⟨sg28291,True.intro,True.intro⟩,⟨sg28293,True.intro,True.intro⟩⟩,⟨sg28296,⟨sg28295,True.intro,True.intro⟩,⟨sg28297,True.intro,True.intro⟩⟩⟩,⟨sg28302,⟨sg28300,⟨sg28299,True.intro,True.intro⟩,⟨sg28301,True.intro,True.intro⟩⟩,⟨sg28304,⟨sg28303,True.intro,True.intro⟩,⟨sg28305,True.intro,True.intro⟩⟩⟩⟩,⟨sg28314,⟨sg28310,⟨sg28308,⟨sg28307,True.intro,True.intro⟩,⟨sg28309,True.intro,True.intro⟩⟩,⟨sg28312,⟨sg28311,True.intro,True.intro⟩,⟨sg28313,True.intro,True.intro⟩⟩⟩,⟨sg28318,⟨sg28316,⟨sg28315,True.intro,True.intro⟩,⟨sg28317,True.intro,True.intro⟩⟩,⟨sg28320,⟨sg28319,True.intro,True.intro⟩,⟨sg28321,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_362All : degreeTree43_362.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28290,degreeTree43_360All,degreeTree43_361All⟩

lemma degreeTree43_363All : degreeTree43_363.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28258,degreeTree43_359All,degreeTree43_362All⟩

lemma degreeTree43_364All : degreeTree43_364.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28193,degreeTree43_354All,degreeTree43_363All⟩

lemma degreeTree43_365All : degreeTree43_365.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28064,degreeTree43_345All,degreeTree43_364All⟩

lemma degreeTree43_366All : degreeTree43_366.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28331,⟨sg28327,⟨sg28325,⟨sg28324,⟨sg28323,True.intro,True.intro⟩,True.intro⟩,⟨sg28326,True.intro,True.intro⟩⟩,⟨sg28329,⟨sg28328,True.intro,True.intro⟩,⟨sg28330,True.intro,True.intro⟩⟩⟩,⟨sg28335,⟨sg28333,⟨sg28332,True.intro,True.intro⟩,⟨sg28334,True.intro,True.intro⟩⟩,⟨sg28337,⟨sg28336,True.intro,True.intro⟩,⟨sg28338,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_367All : degreeTree43_367.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28347,⟨sg28343,⟨sg28341,⟨sg28340,True.intro,True.intro⟩,⟨sg28342,True.intro,True.intro⟩⟩,⟨sg28345,⟨sg28344,True.intro,True.intro⟩,⟨sg28346,True.intro,True.intro⟩⟩⟩,⟨sg28351,⟨sg28349,⟨sg28348,True.intro,True.intro⟩,⟨sg28350,True.intro,True.intro⟩⟩,⟨sg28353,⟨sg28352,True.intro,True.intro⟩,⟨sg28354,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_368All : degreeTree43_368.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28339,degreeTree43_366All,degreeTree43_367All⟩

lemma degreeTree43_369All : degreeTree43_369.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28371,⟨sg28363,⟨sg28359,⟨sg28357,⟨sg28356,True.intro,True.intro⟩,⟨sg28358,True.intro,True.intro⟩⟩,⟨sg28361,⟨sg28360,True.intro,True.intro⟩,⟨sg28362,True.intro,True.intro⟩⟩⟩,⟨sg28367,⟨sg28365,⟨sg28364,True.intro,True.intro⟩,⟨sg28366,True.intro,True.intro⟩⟩,⟨sg28369,⟨sg28368,True.intro,True.intro⟩,⟨sg28370,True.intro,True.intro⟩⟩⟩⟩,⟨sg28379,⟨sg28375,⟨sg28373,⟨sg28372,True.intro,True.intro⟩,⟨sg28374,True.intro,True.intro⟩⟩,⟨sg28377,⟨sg28376,True.intro,True.intro⟩,⟨sg28378,True.intro,True.intro⟩⟩⟩,⟨sg28383,⟨sg28381,⟨sg28380,True.intro,True.intro⟩,⟨sg28382,True.intro,True.intro⟩⟩,⟨sg28385,⟨sg28384,True.intro,True.intro⟩,⟨sg28386,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_370All : degreeTree43_370.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28355,degreeTree43_368All,degreeTree43_369All⟩

lemma degreeTree43_371All : degreeTree43_371.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28403,⟨sg28395,⟨sg28391,⟨sg28389,⟨sg28388,True.intro,True.intro⟩,⟨sg28390,True.intro,True.intro⟩⟩,⟨sg28393,⟨sg28392,True.intro,True.intro⟩,⟨sg28394,True.intro,True.intro⟩⟩⟩,⟨sg28399,⟨sg28397,⟨sg28396,True.intro,True.intro⟩,⟨sg28398,True.intro,True.intro⟩⟩,⟨sg28401,⟨sg28400,True.intro,True.intro⟩,⟨sg28402,True.intro,True.intro⟩⟩⟩⟩,⟨sg28411,⟨sg28407,⟨sg28405,⟨sg28404,True.intro,True.intro⟩,⟨sg28406,True.intro,True.intro⟩⟩,⟨sg28409,⟨sg28408,True.intro,True.intro⟩,⟨sg28410,True.intro,True.intro⟩⟩⟩,⟨sg28415,⟨sg28413,⟨sg28412,True.intro,True.intro⟩,⟨sg28414,True.intro,True.intro⟩⟩,⟨sg28417,⟨sg28416,True.intro,True.intro⟩,⟨sg28418,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_372All : degreeTree43_372.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28435,⟨sg28427,⟨sg28423,⟨sg28421,⟨sg28420,True.intro,True.intro⟩,⟨sg28422,True.intro,True.intro⟩⟩,⟨sg28425,⟨sg28424,True.intro,True.intro⟩,⟨sg28426,True.intro,True.intro⟩⟩⟩,⟨sg28431,⟨sg28429,⟨sg28428,True.intro,True.intro⟩,⟨sg28430,True.intro,True.intro⟩⟩,⟨sg28433,⟨sg28432,True.intro,True.intro⟩,⟨sg28434,True.intro,True.intro⟩⟩⟩⟩,⟨sg28443,⟨sg28439,⟨sg28437,⟨sg28436,True.intro,True.intro⟩,⟨sg28438,True.intro,True.intro⟩⟩,⟨sg28441,⟨sg28440,True.intro,True.intro⟩,⟨sg28442,True.intro,True.intro⟩⟩⟩,⟨sg28447,⟨sg28445,⟨sg28444,True.intro,True.intro⟩,⟨sg28446,True.intro,True.intro⟩⟩,⟨sg28449,⟨sg28448,True.intro,True.intro⟩,⟨sg28450,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_373All : degreeTree43_373.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28419,degreeTree43_371All,degreeTree43_372All⟩

lemma degreeTree43_374All : degreeTree43_374.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28387,degreeTree43_370All,degreeTree43_373All⟩

lemma degreeTree43_375All : degreeTree43_375.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28460,⟨sg28456,⟨sg28454,⟨sg28453,⟨sg28452,True.intro,True.intro⟩,True.intro⟩,⟨sg28455,True.intro,True.intro⟩⟩,⟨sg28458,⟨sg28457,True.intro,True.intro⟩,⟨sg28459,True.intro,True.intro⟩⟩⟩,⟨sg28464,⟨sg28462,⟨sg28461,True.intro,True.intro⟩,⟨sg28463,True.intro,True.intro⟩⟩,⟨sg28466,⟨sg28465,True.intro,True.intro⟩,⟨sg28467,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_376All : degreeTree43_376.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28476,⟨sg28472,⟨sg28470,⟨sg28469,True.intro,True.intro⟩,⟨sg28471,True.intro,True.intro⟩⟩,⟨sg28474,⟨sg28473,True.intro,True.intro⟩,⟨sg28475,True.intro,True.intro⟩⟩⟩,⟨sg28480,⟨sg28478,⟨sg28477,True.intro,True.intro⟩,⟨sg28479,True.intro,True.intro⟩⟩,⟨sg28482,⟨sg28481,True.intro,True.intro⟩,⟨sg28483,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_377All : degreeTree43_377.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28468,degreeTree43_375All,degreeTree43_376All⟩

lemma degreeTree43_378All : degreeTree43_378.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28500,⟨sg28492,⟨sg28488,⟨sg28486,⟨sg28485,True.intro,True.intro⟩,⟨sg28487,True.intro,True.intro⟩⟩,⟨sg28490,⟨sg28489,True.intro,True.intro⟩,⟨sg28491,True.intro,True.intro⟩⟩⟩,⟨sg28496,⟨sg28494,⟨sg28493,True.intro,True.intro⟩,⟨sg28495,True.intro,True.intro⟩⟩,⟨sg28498,⟨sg28497,True.intro,True.intro⟩,⟨sg28499,True.intro,True.intro⟩⟩⟩⟩,⟨sg28508,⟨sg28504,⟨sg28502,⟨sg28501,True.intro,True.intro⟩,⟨sg28503,True.intro,True.intro⟩⟩,⟨sg28506,⟨sg28505,True.intro,True.intro⟩,⟨sg28507,True.intro,True.intro⟩⟩⟩,⟨sg28512,⟨sg28510,⟨sg28509,True.intro,True.intro⟩,⟨sg28511,True.intro,True.intro⟩⟩,⟨sg28514,⟨sg28513,True.intro,True.intro⟩,⟨sg28515,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_379All : degreeTree43_379.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28484,degreeTree43_377All,degreeTree43_378All⟩

lemma degreeTree43_380All : degreeTree43_380.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28532,⟨sg28524,⟨sg28520,⟨sg28518,⟨sg28517,True.intro,True.intro⟩,⟨sg28519,True.intro,True.intro⟩⟩,⟨sg28522,⟨sg28521,True.intro,True.intro⟩,⟨sg28523,True.intro,True.intro⟩⟩⟩,⟨sg28528,⟨sg28526,⟨sg28525,True.intro,True.intro⟩,⟨sg28527,True.intro,True.intro⟩⟩,⟨sg28530,⟨sg28529,True.intro,True.intro⟩,⟨sg28531,True.intro,True.intro⟩⟩⟩⟩,⟨sg28540,⟨sg28536,⟨sg28534,⟨sg28533,True.intro,True.intro⟩,⟨sg28535,True.intro,True.intro⟩⟩,⟨sg28538,⟨sg28537,True.intro,True.intro⟩,⟨sg28539,True.intro,True.intro⟩⟩⟩,⟨sg28544,⟨sg28542,⟨sg28541,True.intro,True.intro⟩,⟨sg28543,True.intro,True.intro⟩⟩,⟨sg28546,⟨sg28545,True.intro,True.intro⟩,⟨sg28547,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_381All : degreeTree43_381.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28564,⟨sg28556,⟨sg28552,⟨sg28550,⟨sg28549,True.intro,True.intro⟩,⟨sg28551,True.intro,True.intro⟩⟩,⟨sg28554,⟨sg28553,True.intro,True.intro⟩,⟨sg28555,True.intro,True.intro⟩⟩⟩,⟨sg28560,⟨sg28558,⟨sg28557,True.intro,True.intro⟩,⟨sg28559,True.intro,True.intro⟩⟩,⟨sg28562,⟨sg28561,True.intro,True.intro⟩,⟨sg28563,True.intro,True.intro⟩⟩⟩⟩,⟨sg28572,⟨sg28568,⟨sg28566,⟨sg28565,True.intro,True.intro⟩,⟨sg28567,True.intro,True.intro⟩⟩,⟨sg28570,⟨sg28569,True.intro,True.intro⟩,⟨sg28571,True.intro,True.intro⟩⟩⟩,⟨sg28576,⟨sg28574,⟨sg28573,True.intro,True.intro⟩,⟨sg28575,True.intro,True.intro⟩⟩,⟨sg28578,⟨sg28577,True.intro,True.intro⟩,⟨sg28579,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_382All : degreeTree43_382.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28548,degreeTree43_380All,degreeTree43_381All⟩

lemma degreeTree43_383All : degreeTree43_383.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28516,degreeTree43_379All,degreeTree43_382All⟩

lemma degreeTree43_384All : degreeTree43_384.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28451,degreeTree43_374All,degreeTree43_383All⟩

lemma degreeTree43_385All : degreeTree43_385.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28589,⟨sg28585,⟨sg28583,⟨sg28582,⟨sg28581,True.intro,True.intro⟩,True.intro⟩,⟨sg28584,True.intro,True.intro⟩⟩,⟨sg28587,⟨sg28586,True.intro,True.intro⟩,⟨sg28588,True.intro,True.intro⟩⟩⟩,⟨sg28593,⟨sg28591,⟨sg28590,True.intro,True.intro⟩,⟨sg28592,True.intro,True.intro⟩⟩,⟨sg28595,⟨sg28594,True.intro,True.intro⟩,⟨sg28596,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_386All : degreeTree43_386.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28605,⟨sg28601,⟨sg28599,⟨sg28598,True.intro,True.intro⟩,⟨sg28600,True.intro,True.intro⟩⟩,⟨sg28603,⟨sg28602,True.intro,True.intro⟩,⟨sg28604,True.intro,True.intro⟩⟩⟩,⟨sg28609,⟨sg28607,⟨sg28606,True.intro,True.intro⟩,⟨sg28608,True.intro,True.intro⟩⟩,⟨sg28611,⟨sg28610,True.intro,True.intro⟩,⟨sg28612,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_387All : degreeTree43_387.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28597,degreeTree43_385All,degreeTree43_386All⟩

lemma degreeTree43_388All : degreeTree43_388.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28629,⟨sg28621,⟨sg28617,⟨sg28615,⟨sg28614,True.intro,True.intro⟩,⟨sg28616,True.intro,True.intro⟩⟩,⟨sg28619,⟨sg28618,True.intro,True.intro⟩,⟨sg28620,True.intro,True.intro⟩⟩⟩,⟨sg28625,⟨sg28623,⟨sg28622,True.intro,True.intro⟩,⟨sg28624,True.intro,True.intro⟩⟩,⟨sg28627,⟨sg28626,True.intro,True.intro⟩,⟨sg28628,True.intro,True.intro⟩⟩⟩⟩,⟨sg28637,⟨sg28633,⟨sg28631,⟨sg28630,True.intro,True.intro⟩,⟨sg28632,True.intro,True.intro⟩⟩,⟨sg28635,⟨sg28634,True.intro,True.intro⟩,⟨sg28636,True.intro,True.intro⟩⟩⟩,⟨sg28641,⟨sg28639,⟨sg28638,True.intro,True.intro⟩,⟨sg28640,True.intro,True.intro⟩⟩,⟨sg28643,⟨sg28642,True.intro,True.intro⟩,⟨sg28644,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_389All : degreeTree43_389.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28613,degreeTree43_387All,degreeTree43_388All⟩

lemma degreeTree43_390All : degreeTree43_390.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28661,⟨sg28653,⟨sg28649,⟨sg28647,⟨sg28646,True.intro,True.intro⟩,⟨sg28648,True.intro,True.intro⟩⟩,⟨sg28651,⟨sg28650,True.intro,True.intro⟩,⟨sg28652,True.intro,True.intro⟩⟩⟩,⟨sg28657,⟨sg28655,⟨sg28654,True.intro,True.intro⟩,⟨sg28656,True.intro,True.intro⟩⟩,⟨sg28659,⟨sg28658,True.intro,True.intro⟩,⟨sg28660,True.intro,True.intro⟩⟩⟩⟩,⟨sg28669,⟨sg28665,⟨sg28663,⟨sg28662,True.intro,True.intro⟩,⟨sg28664,True.intro,True.intro⟩⟩,⟨sg28667,⟨sg28666,True.intro,True.intro⟩,⟨sg28668,True.intro,True.intro⟩⟩⟩,⟨sg28673,⟨sg28671,⟨sg28670,True.intro,True.intro⟩,⟨sg28672,True.intro,True.intro⟩⟩,⟨sg28675,⟨sg28674,True.intro,True.intro⟩,⟨sg28676,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_391All : degreeTree43_391.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28693,⟨sg28685,⟨sg28681,⟨sg28679,⟨sg28678,True.intro,True.intro⟩,⟨sg28680,True.intro,True.intro⟩⟩,⟨sg28683,⟨sg28682,True.intro,True.intro⟩,⟨sg28684,True.intro,True.intro⟩⟩⟩,⟨sg28689,⟨sg28687,⟨sg28686,True.intro,True.intro⟩,⟨sg28688,True.intro,True.intro⟩⟩,⟨sg28691,⟨sg28690,True.intro,True.intro⟩,⟨sg28692,True.intro,True.intro⟩⟩⟩⟩,⟨sg28701,⟨sg28697,⟨sg28695,⟨sg28694,True.intro,True.intro⟩,⟨sg28696,True.intro,True.intro⟩⟩,⟨sg28699,⟨sg28698,True.intro,True.intro⟩,⟨sg28700,True.intro,True.intro⟩⟩⟩,⟨sg28705,⟨sg28703,⟨sg28702,True.intro,True.intro⟩,⟨sg28704,True.intro,True.intro⟩⟩,⟨sg28707,⟨sg28706,True.intro,True.intro⟩,⟨sg28708,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_392All : degreeTree43_392.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28677,degreeTree43_390All,degreeTree43_391All⟩

lemma degreeTree43_393All : degreeTree43_393.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28645,degreeTree43_389All,degreeTree43_392All⟩

lemma degreeTree43_394All : degreeTree43_394.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28718,⟨sg28714,⟨sg28712,⟨sg28711,⟨sg28710,True.intro,True.intro⟩,True.intro⟩,⟨sg28713,True.intro,True.intro⟩⟩,⟨sg28716,⟨sg28715,True.intro,True.intro⟩,⟨sg28717,True.intro,True.intro⟩⟩⟩,⟨sg28722,⟨sg28720,⟨sg28719,True.intro,True.intro⟩,⟨sg28721,True.intro,True.intro⟩⟩,⟨sg28724,⟨sg28723,True.intro,True.intro⟩,⟨sg28725,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_395All : degreeTree43_395.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28734,⟨sg28730,⟨sg28728,⟨sg28727,True.intro,True.intro⟩,⟨sg28729,True.intro,True.intro⟩⟩,⟨sg28732,⟨sg28731,True.intro,True.intro⟩,⟨sg28733,True.intro,True.intro⟩⟩⟩,⟨sg28738,⟨sg28736,⟨sg28735,True.intro,True.intro⟩,⟨sg28737,True.intro,True.intro⟩⟩,⟨sg28740,⟨sg28739,True.intro,True.intro⟩,⟨sg28741,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_396All : degreeTree43_396.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28726,degreeTree43_394All,degreeTree43_395All⟩

lemma degreeTree43_397All : degreeTree43_397.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28758,⟨sg28750,⟨sg28746,⟨sg28744,⟨sg28743,True.intro,True.intro⟩,⟨sg28745,True.intro,True.intro⟩⟩,⟨sg28748,⟨sg28747,True.intro,True.intro⟩,⟨sg28749,True.intro,True.intro⟩⟩⟩,⟨sg28754,⟨sg28752,⟨sg28751,True.intro,True.intro⟩,⟨sg28753,True.intro,True.intro⟩⟩,⟨sg28756,⟨sg28755,True.intro,True.intro⟩,⟨sg28757,True.intro,True.intro⟩⟩⟩⟩,⟨sg28766,⟨sg28762,⟨sg28760,⟨sg28759,True.intro,True.intro⟩,⟨sg28761,True.intro,True.intro⟩⟩,⟨sg28764,⟨sg28763,True.intro,True.intro⟩,⟨sg28765,True.intro,True.intro⟩⟩⟩,⟨sg28770,⟨sg28768,⟨sg28767,True.intro,True.intro⟩,⟨sg28769,True.intro,True.intro⟩⟩,⟨sg28772,⟨sg28771,True.intro,True.intro⟩,⟨sg28773,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_398All : degreeTree43_398.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28742,degreeTree43_396All,degreeTree43_397All⟩

lemma degreeTree43_399All : degreeTree43_399.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28790,⟨sg28782,⟨sg28778,⟨sg28776,⟨sg28775,True.intro,True.intro⟩,⟨sg28777,True.intro,True.intro⟩⟩,⟨sg28780,⟨sg28779,True.intro,True.intro⟩,⟨sg28781,True.intro,True.intro⟩⟩⟩,⟨sg28786,⟨sg28784,⟨sg28783,True.intro,True.intro⟩,⟨sg28785,True.intro,True.intro⟩⟩,⟨sg28788,⟨sg28787,True.intro,True.intro⟩,⟨sg28789,True.intro,True.intro⟩⟩⟩⟩,⟨sg28798,⟨sg28794,⟨sg28792,⟨sg28791,True.intro,True.intro⟩,⟨sg28793,True.intro,True.intro⟩⟩,⟨sg28796,⟨sg28795,True.intro,True.intro⟩,⟨sg28797,True.intro,True.intro⟩⟩⟩,⟨sg28802,⟨sg28800,⟨sg28799,True.intro,True.intro⟩,⟨sg28801,True.intro,True.intro⟩⟩,⟨sg28804,⟨sg28803,True.intro,True.intro⟩,⟨sg28805,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_400All : degreeTree43_400.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28822,⟨sg28814,⟨sg28810,⟨sg28808,⟨sg28807,True.intro,True.intro⟩,⟨sg28809,True.intro,True.intro⟩⟩,⟨sg28812,⟨sg28811,True.intro,True.intro⟩,⟨sg28813,True.intro,True.intro⟩⟩⟩,⟨sg28818,⟨sg28816,⟨sg28815,True.intro,True.intro⟩,⟨sg28817,True.intro,True.intro⟩⟩,⟨sg28820,⟨sg28819,True.intro,True.intro⟩,⟨sg28821,True.intro,True.intro⟩⟩⟩⟩,⟨sg28830,⟨sg28826,⟨sg28824,⟨sg28823,True.intro,True.intro⟩,⟨sg28825,True.intro,True.intro⟩⟩,⟨sg28828,⟨sg28827,True.intro,True.intro⟩,⟨sg28829,True.intro,True.intro⟩⟩⟩,⟨sg28834,⟨sg28832,⟨sg28831,True.intro,True.intro⟩,⟨sg28833,True.intro,True.intro⟩⟩,⟨sg28836,⟨sg28835,True.intro,True.intro⟩,⟨sg28837,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_401All : degreeTree43_401.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28806,degreeTree43_399All,degreeTree43_400All⟩

lemma degreeTree43_402All : degreeTree43_402.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28774,degreeTree43_398All,degreeTree43_401All⟩

lemma degreeTree43_403All : degreeTree43_403.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28709,degreeTree43_393All,degreeTree43_402All⟩

lemma degreeTree43_404All : degreeTree43_404.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28580,degreeTree43_384All,degreeTree43_403All⟩

lemma degreeTree43_405All : degreeTree43_405.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28322,degreeTree43_365All,degreeTree43_404All⟩

lemma degreeTree43_406All : degreeTree43_406.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28847,⟨sg28843,⟨sg28841,⟨sg28840,⟨sg28839,True.intro,True.intro⟩,True.intro⟩,⟨sg28842,True.intro,True.intro⟩⟩,⟨sg28845,⟨sg28844,True.intro,True.intro⟩,⟨sg28846,True.intro,True.intro⟩⟩⟩,⟨sg28851,⟨sg28849,⟨sg28848,True.intro,True.intro⟩,⟨sg28850,True.intro,True.intro⟩⟩,⟨sg28853,⟨sg28852,True.intro,True.intro⟩,⟨sg28854,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_407All : degreeTree43_407.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28863,⟨sg28859,⟨sg28857,⟨sg28856,True.intro,True.intro⟩,⟨sg28858,True.intro,True.intro⟩⟩,⟨sg28861,⟨sg28860,True.intro,True.intro⟩,⟨sg28862,True.intro,True.intro⟩⟩⟩,⟨sg28867,⟨sg28865,⟨sg28864,True.intro,True.intro⟩,⟨sg28866,True.intro,True.intro⟩⟩,⟨sg28869,⟨sg28868,True.intro,True.intro⟩,⟨sg28870,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_408All : degreeTree43_408.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28855,degreeTree43_406All,degreeTree43_407All⟩

lemma degreeTree43_409All : degreeTree43_409.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28887,⟨sg28879,⟨sg28875,⟨sg28873,⟨sg28872,True.intro,True.intro⟩,⟨sg28874,True.intro,True.intro⟩⟩,⟨sg28877,⟨sg28876,True.intro,True.intro⟩,⟨sg28878,True.intro,True.intro⟩⟩⟩,⟨sg28883,⟨sg28881,⟨sg28880,True.intro,True.intro⟩,⟨sg28882,True.intro,True.intro⟩⟩,⟨sg28885,⟨sg28884,True.intro,True.intro⟩,⟨sg28886,True.intro,True.intro⟩⟩⟩⟩,⟨sg28895,⟨sg28891,⟨sg28889,⟨sg28888,True.intro,True.intro⟩,⟨sg28890,True.intro,True.intro⟩⟩,⟨sg28893,⟨sg28892,True.intro,True.intro⟩,⟨sg28894,True.intro,True.intro⟩⟩⟩,⟨sg28899,⟨sg28897,⟨sg28896,True.intro,True.intro⟩,⟨sg28898,True.intro,True.intro⟩⟩,⟨sg28901,⟨sg28900,True.intro,True.intro⟩,⟨sg28902,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_410All : degreeTree43_410.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28871,degreeTree43_408All,degreeTree43_409All⟩

lemma degreeTree43_411All : degreeTree43_411.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28919,⟨sg28911,⟨sg28907,⟨sg28905,⟨sg28904,True.intro,True.intro⟩,⟨sg28906,True.intro,True.intro⟩⟩,⟨sg28909,⟨sg28908,True.intro,True.intro⟩,⟨sg28910,True.intro,True.intro⟩⟩⟩,⟨sg28915,⟨sg28913,⟨sg28912,True.intro,True.intro⟩,⟨sg28914,True.intro,True.intro⟩⟩,⟨sg28917,⟨sg28916,True.intro,True.intro⟩,⟨sg28918,True.intro,True.intro⟩⟩⟩⟩,⟨sg28927,⟨sg28923,⟨sg28921,⟨sg28920,True.intro,True.intro⟩,⟨sg28922,True.intro,True.intro⟩⟩,⟨sg28925,⟨sg28924,True.intro,True.intro⟩,⟨sg28926,True.intro,True.intro⟩⟩⟩,⟨sg28931,⟨sg28929,⟨sg28928,True.intro,True.intro⟩,⟨sg28930,True.intro,True.intro⟩⟩,⟨sg28933,⟨sg28932,True.intro,True.intro⟩,⟨sg28934,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_412All : degreeTree43_412.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28951,⟨sg28943,⟨sg28939,⟨sg28937,⟨sg28936,True.intro,True.intro⟩,⟨sg28938,True.intro,True.intro⟩⟩,⟨sg28941,⟨sg28940,True.intro,True.intro⟩,⟨sg28942,True.intro,True.intro⟩⟩⟩,⟨sg28947,⟨sg28945,⟨sg28944,True.intro,True.intro⟩,⟨sg28946,True.intro,True.intro⟩⟩,⟨sg28949,⟨sg28948,True.intro,True.intro⟩,⟨sg28950,True.intro,True.intro⟩⟩⟩⟩,⟨sg28959,⟨sg28955,⟨sg28953,⟨sg28952,True.intro,True.intro⟩,⟨sg28954,True.intro,True.intro⟩⟩,⟨sg28957,⟨sg28956,True.intro,True.intro⟩,⟨sg28958,True.intro,True.intro⟩⟩⟩,⟨sg28963,⟨sg28961,⟨sg28960,True.intro,True.intro⟩,⟨sg28962,True.intro,True.intro⟩⟩,⟨sg28965,⟨sg28964,True.intro,True.intro⟩,⟨sg28966,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_413All : degreeTree43_413.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28935,degreeTree43_411All,degreeTree43_412All⟩

lemma degreeTree43_414All : degreeTree43_414.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28903,degreeTree43_410All,degreeTree43_413All⟩

lemma degreeTree43_415All : degreeTree43_415.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28976,⟨sg28972,⟨sg28970,⟨sg28969,⟨sg28968,True.intro,True.intro⟩,True.intro⟩,⟨sg28971,True.intro,True.intro⟩⟩,⟨sg28974,⟨sg28973,True.intro,True.intro⟩,⟨sg28975,True.intro,True.intro⟩⟩⟩,⟨sg28980,⟨sg28978,⟨sg28977,True.intro,True.intro⟩,⟨sg28979,True.intro,True.intro⟩⟩,⟨sg28982,⟨sg28981,True.intro,True.intro⟩,⟨sg28983,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_416All : degreeTree43_416.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28992,⟨sg28988,⟨sg28986,⟨sg28985,True.intro,True.intro⟩,⟨sg28987,True.intro,True.intro⟩⟩,⟨sg28990,⟨sg28989,True.intro,True.intro⟩,⟨sg28991,True.intro,True.intro⟩⟩⟩,⟨sg28996,⟨sg28994,⟨sg28993,True.intro,True.intro⟩,⟨sg28995,True.intro,True.intro⟩⟩,⟨sg28998,⟨sg28997,True.intro,True.intro⟩,⟨sg28999,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_417All : degreeTree43_417.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28984,degreeTree43_415All,degreeTree43_416All⟩

lemma degreeTree43_418All : degreeTree43_418.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29016,⟨sg29008,⟨sg29004,⟨sg29002,⟨sg29001,True.intro,True.intro⟩,⟨sg29003,True.intro,True.intro⟩⟩,⟨sg29006,⟨sg29005,True.intro,True.intro⟩,⟨sg29007,True.intro,True.intro⟩⟩⟩,⟨sg29012,⟨sg29010,⟨sg29009,True.intro,True.intro⟩,⟨sg29011,True.intro,True.intro⟩⟩,⟨sg29014,⟨sg29013,True.intro,True.intro⟩,⟨sg29015,True.intro,True.intro⟩⟩⟩⟩,⟨sg29024,⟨sg29020,⟨sg29018,⟨sg29017,True.intro,True.intro⟩,⟨sg29019,True.intro,True.intro⟩⟩,⟨sg29022,⟨sg29021,True.intro,True.intro⟩,⟨sg29023,True.intro,True.intro⟩⟩⟩,⟨sg29028,⟨sg29026,⟨sg29025,True.intro,True.intro⟩,⟨sg29027,True.intro,True.intro⟩⟩,⟨sg29030,⟨sg29029,True.intro,True.intro⟩,⟨sg29031,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_419All : degreeTree43_419.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29000,degreeTree43_417All,degreeTree43_418All⟩

lemma degreeTree43_420All : degreeTree43_420.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29048,⟨sg29040,⟨sg29036,⟨sg29034,⟨sg29033,True.intro,True.intro⟩,⟨sg29035,True.intro,True.intro⟩⟩,⟨sg29038,⟨sg29037,True.intro,True.intro⟩,⟨sg29039,True.intro,True.intro⟩⟩⟩,⟨sg29044,⟨sg29042,⟨sg29041,True.intro,True.intro⟩,⟨sg29043,True.intro,True.intro⟩⟩,⟨sg29046,⟨sg29045,True.intro,True.intro⟩,⟨sg29047,True.intro,True.intro⟩⟩⟩⟩,⟨sg29056,⟨sg29052,⟨sg29050,⟨sg29049,True.intro,True.intro⟩,⟨sg29051,True.intro,True.intro⟩⟩,⟨sg29054,⟨sg29053,True.intro,True.intro⟩,⟨sg29055,True.intro,True.intro⟩⟩⟩,⟨sg29060,⟨sg29058,⟨sg29057,True.intro,True.intro⟩,⟨sg29059,True.intro,True.intro⟩⟩,⟨sg29062,⟨sg29061,True.intro,True.intro⟩,⟨sg29063,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_421All : degreeTree43_421.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29080,⟨sg29072,⟨sg29068,⟨sg29066,⟨sg29065,True.intro,True.intro⟩,⟨sg29067,True.intro,True.intro⟩⟩,⟨sg29070,⟨sg29069,True.intro,True.intro⟩,⟨sg29071,True.intro,True.intro⟩⟩⟩,⟨sg29076,⟨sg29074,⟨sg29073,True.intro,True.intro⟩,⟨sg29075,True.intro,True.intro⟩⟩,⟨sg29078,⟨sg29077,True.intro,True.intro⟩,⟨sg29079,True.intro,True.intro⟩⟩⟩⟩,⟨sg29088,⟨sg29084,⟨sg29082,⟨sg29081,True.intro,True.intro⟩,⟨sg29083,True.intro,True.intro⟩⟩,⟨sg29086,⟨sg29085,True.intro,True.intro⟩,⟨sg29087,True.intro,True.intro⟩⟩⟩,⟨sg29092,⟨sg29090,⟨sg29089,True.intro,True.intro⟩,⟨sg29091,True.intro,True.intro⟩⟩,⟨sg29094,⟨sg29093,True.intro,True.intro⟩,⟨sg29095,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_422All : degreeTree43_422.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29064,degreeTree43_420All,degreeTree43_421All⟩

lemma degreeTree43_423All : degreeTree43_423.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29032,degreeTree43_419All,degreeTree43_422All⟩

lemma degreeTree43_424All : degreeTree43_424.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28967,degreeTree43_414All,degreeTree43_423All⟩

lemma degreeTree43_425All : degreeTree43_425.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29105,⟨sg29101,⟨sg29099,⟨sg29098,⟨sg29097,True.intro,True.intro⟩,True.intro⟩,⟨sg29100,True.intro,True.intro⟩⟩,⟨sg29103,⟨sg29102,True.intro,True.intro⟩,⟨sg29104,True.intro,True.intro⟩⟩⟩,⟨sg29109,⟨sg29107,⟨sg29106,True.intro,True.intro⟩,⟨sg29108,True.intro,True.intro⟩⟩,⟨sg29111,⟨sg29110,True.intro,True.intro⟩,⟨sg29112,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_426All : degreeTree43_426.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29121,⟨sg29117,⟨sg29115,⟨sg29114,True.intro,True.intro⟩,⟨sg29116,True.intro,True.intro⟩⟩,⟨sg29119,⟨sg29118,True.intro,True.intro⟩,⟨sg29120,True.intro,True.intro⟩⟩⟩,⟨sg29125,⟨sg29123,⟨sg29122,True.intro,True.intro⟩,⟨sg29124,True.intro,True.intro⟩⟩,⟨sg29127,⟨sg29126,True.intro,True.intro⟩,⟨sg29128,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_427All : degreeTree43_427.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29113,degreeTree43_425All,degreeTree43_426All⟩

lemma degreeTree43_428All : degreeTree43_428.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29145,⟨sg29137,⟨sg29133,⟨sg29131,⟨sg29130,True.intro,True.intro⟩,⟨sg29132,True.intro,True.intro⟩⟩,⟨sg29135,⟨sg29134,True.intro,True.intro⟩,⟨sg29136,True.intro,True.intro⟩⟩⟩,⟨sg29141,⟨sg29139,⟨sg29138,True.intro,True.intro⟩,⟨sg29140,True.intro,True.intro⟩⟩,⟨sg29143,⟨sg29142,True.intro,True.intro⟩,⟨sg29144,True.intro,True.intro⟩⟩⟩⟩,⟨sg29153,⟨sg29149,⟨sg29147,⟨sg29146,True.intro,True.intro⟩,⟨sg29148,True.intro,True.intro⟩⟩,⟨sg29151,⟨sg29150,True.intro,True.intro⟩,⟨sg29152,True.intro,True.intro⟩⟩⟩,⟨sg29157,⟨sg29155,⟨sg29154,True.intro,True.intro⟩,⟨sg29156,True.intro,True.intro⟩⟩,⟨sg29159,⟨sg29158,True.intro,True.intro⟩,⟨sg29160,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_429All : degreeTree43_429.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29129,degreeTree43_427All,degreeTree43_428All⟩

lemma degreeTree43_430All : degreeTree43_430.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29177,⟨sg29169,⟨sg29165,⟨sg29163,⟨sg29162,True.intro,True.intro⟩,⟨sg29164,True.intro,True.intro⟩⟩,⟨sg29167,⟨sg29166,True.intro,True.intro⟩,⟨sg29168,True.intro,True.intro⟩⟩⟩,⟨sg29173,⟨sg29171,⟨sg29170,True.intro,True.intro⟩,⟨sg29172,True.intro,True.intro⟩⟩,⟨sg29175,⟨sg29174,True.intro,True.intro⟩,⟨sg29176,True.intro,True.intro⟩⟩⟩⟩,⟨sg29185,⟨sg29181,⟨sg29179,⟨sg29178,True.intro,True.intro⟩,⟨sg29180,True.intro,True.intro⟩⟩,⟨sg29183,⟨sg29182,True.intro,True.intro⟩,⟨sg29184,True.intro,True.intro⟩⟩⟩,⟨sg29189,⟨sg29187,⟨sg29186,True.intro,True.intro⟩,⟨sg29188,True.intro,True.intro⟩⟩,⟨sg29191,⟨sg29190,True.intro,True.intro⟩,⟨sg29192,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_431All : degreeTree43_431.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29209,⟨sg29201,⟨sg29197,⟨sg29195,⟨sg29194,True.intro,True.intro⟩,⟨sg29196,True.intro,True.intro⟩⟩,⟨sg29199,⟨sg29198,True.intro,True.intro⟩,⟨sg29200,True.intro,True.intro⟩⟩⟩,⟨sg29205,⟨sg29203,⟨sg29202,True.intro,True.intro⟩,⟨sg29204,True.intro,True.intro⟩⟩,⟨sg29207,⟨sg29206,True.intro,True.intro⟩,⟨sg29208,True.intro,True.intro⟩⟩⟩⟩,⟨sg29217,⟨sg29213,⟨sg29211,⟨sg29210,True.intro,True.intro⟩,⟨sg29212,True.intro,True.intro⟩⟩,⟨sg29215,⟨sg29214,True.intro,True.intro⟩,⟨sg29216,True.intro,True.intro⟩⟩⟩,⟨sg29221,⟨sg29219,⟨sg29218,True.intro,True.intro⟩,⟨sg29220,True.intro,True.intro⟩⟩,⟨sg29223,⟨sg29222,True.intro,True.intro⟩,⟨sg29224,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_432All : degreeTree43_432.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29193,degreeTree43_430All,degreeTree43_431All⟩

lemma degreeTree43_433All : degreeTree43_433.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29161,degreeTree43_429All,degreeTree43_432All⟩

lemma degreeTree43_434All : degreeTree43_434.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29234,⟨sg29230,⟨sg29228,⟨sg29227,⟨sg29226,True.intro,True.intro⟩,True.intro⟩,⟨sg29229,True.intro,True.intro⟩⟩,⟨sg29232,⟨sg29231,True.intro,True.intro⟩,⟨sg29233,True.intro,True.intro⟩⟩⟩,⟨sg29238,⟨sg29236,⟨sg29235,True.intro,True.intro⟩,⟨sg29237,True.intro,True.intro⟩⟩,⟨sg29240,⟨sg29239,True.intro,True.intro⟩,⟨sg29241,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_435All : degreeTree43_435.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29250,⟨sg29246,⟨sg29244,⟨sg29243,True.intro,True.intro⟩,⟨sg29245,True.intro,True.intro⟩⟩,⟨sg29248,⟨sg29247,True.intro,True.intro⟩,⟨sg29249,True.intro,True.intro⟩⟩⟩,⟨sg29254,⟨sg29252,⟨sg29251,True.intro,True.intro⟩,⟨sg29253,True.intro,True.intro⟩⟩,⟨sg29256,⟨sg29255,True.intro,True.intro⟩,⟨sg29257,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_436All : degreeTree43_436.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29242,degreeTree43_434All,degreeTree43_435All⟩

lemma degreeTree43_437All : degreeTree43_437.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29274,⟨sg29266,⟨sg29262,⟨sg29260,⟨sg29259,True.intro,True.intro⟩,⟨sg29261,True.intro,True.intro⟩⟩,⟨sg29264,⟨sg29263,True.intro,True.intro⟩,⟨sg29265,True.intro,True.intro⟩⟩⟩,⟨sg29270,⟨sg29268,⟨sg29267,True.intro,True.intro⟩,⟨sg29269,True.intro,True.intro⟩⟩,⟨sg29272,⟨sg29271,True.intro,True.intro⟩,⟨sg29273,True.intro,True.intro⟩⟩⟩⟩,⟨sg29282,⟨sg29278,⟨sg29276,⟨sg29275,True.intro,True.intro⟩,⟨sg29277,True.intro,True.intro⟩⟩,⟨sg29280,⟨sg29279,True.intro,True.intro⟩,⟨sg29281,True.intro,True.intro⟩⟩⟩,⟨sg29286,⟨sg29284,⟨sg29283,True.intro,True.intro⟩,⟨sg29285,True.intro,True.intro⟩⟩,⟨sg29288,⟨sg29287,True.intro,True.intro⟩,⟨sg29289,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_438All : degreeTree43_438.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29258,degreeTree43_436All,degreeTree43_437All⟩

lemma degreeTree43_439All : degreeTree43_439.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29306,⟨sg29298,⟨sg29294,⟨sg29292,⟨sg29291,True.intro,True.intro⟩,⟨sg29293,True.intro,True.intro⟩⟩,⟨sg29296,⟨sg29295,True.intro,True.intro⟩,⟨sg29297,True.intro,True.intro⟩⟩⟩,⟨sg29302,⟨sg29300,⟨sg29299,True.intro,True.intro⟩,⟨sg29301,True.intro,True.intro⟩⟩,⟨sg29304,⟨sg29303,True.intro,True.intro⟩,⟨sg29305,True.intro,True.intro⟩⟩⟩⟩,⟨sg29314,⟨sg29310,⟨sg29308,⟨sg29307,True.intro,True.intro⟩,⟨sg29309,True.intro,True.intro⟩⟩,⟨sg29312,⟨sg29311,True.intro,True.intro⟩,⟨sg29313,True.intro,True.intro⟩⟩⟩,⟨sg29318,⟨sg29316,⟨sg29315,True.intro,True.intro⟩,⟨sg29317,True.intro,True.intro⟩⟩,⟨sg29320,⟨sg29319,True.intro,True.intro⟩,⟨sg29321,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_440All : degreeTree43_440.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29338,⟨sg29330,⟨sg29326,⟨sg29324,⟨sg29323,True.intro,True.intro⟩,⟨sg29325,True.intro,True.intro⟩⟩,⟨sg29328,⟨sg29327,True.intro,True.intro⟩,⟨sg29329,True.intro,True.intro⟩⟩⟩,⟨sg29334,⟨sg29332,⟨sg29331,True.intro,True.intro⟩,⟨sg29333,True.intro,True.intro⟩⟩,⟨sg29336,⟨sg29335,True.intro,True.intro⟩,⟨sg29337,True.intro,True.intro⟩⟩⟩⟩,⟨sg29346,⟨sg29342,⟨sg29340,⟨sg29339,True.intro,True.intro⟩,⟨sg29341,True.intro,True.intro⟩⟩,⟨sg29344,⟨sg29343,True.intro,True.intro⟩,⟨sg29345,True.intro,True.intro⟩⟩⟩,⟨sg29350,⟨sg29348,⟨sg29347,True.intro,True.intro⟩,⟨sg29349,True.intro,True.intro⟩⟩,⟨sg29352,⟨sg29351,True.intro,True.intro⟩,⟨sg29353,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_441All : degreeTree43_441.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29322,degreeTree43_439All,degreeTree43_440All⟩

lemma degreeTree43_442All : degreeTree43_442.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29290,degreeTree43_438All,degreeTree43_441All⟩

lemma degreeTree43_443All : degreeTree43_443.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29225,degreeTree43_433All,degreeTree43_442All⟩

lemma degreeTree43_444All : degreeTree43_444.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29096,degreeTree43_424All,degreeTree43_443All⟩

lemma degreeTree43_445All : degreeTree43_445.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29363,⟨sg29359,⟨sg29357,⟨sg29356,⟨sg29355,True.intro,True.intro⟩,True.intro⟩,⟨sg29358,True.intro,True.intro⟩⟩,⟨sg29361,⟨sg29360,True.intro,True.intro⟩,⟨sg29362,True.intro,True.intro⟩⟩⟩,⟨sg29367,⟨sg29365,⟨sg29364,True.intro,True.intro⟩,⟨sg29366,True.intro,True.intro⟩⟩,⟨sg29369,⟨sg29368,True.intro,True.intro⟩,⟨sg29370,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_446All : degreeTree43_446.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29379,⟨sg29375,⟨sg29373,⟨sg29372,True.intro,True.intro⟩,⟨sg29374,True.intro,True.intro⟩⟩,⟨sg29377,⟨sg29376,True.intro,True.intro⟩,⟨sg29378,True.intro,True.intro⟩⟩⟩,⟨sg29383,⟨sg29381,⟨sg29380,True.intro,True.intro⟩,⟨sg29382,True.intro,True.intro⟩⟩,⟨sg29385,⟨sg29384,True.intro,True.intro⟩,⟨sg29386,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_447All : degreeTree43_447.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29371,degreeTree43_445All,degreeTree43_446All⟩

lemma degreeTree43_448All : degreeTree43_448.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29403,⟨sg29395,⟨sg29391,⟨sg29389,⟨sg29388,True.intro,True.intro⟩,⟨sg29390,True.intro,True.intro⟩⟩,⟨sg29393,⟨sg29392,True.intro,True.intro⟩,⟨sg29394,True.intro,True.intro⟩⟩⟩,⟨sg29399,⟨sg29397,⟨sg29396,True.intro,True.intro⟩,⟨sg29398,True.intro,True.intro⟩⟩,⟨sg29401,⟨sg29400,True.intro,True.intro⟩,⟨sg29402,True.intro,True.intro⟩⟩⟩⟩,⟨sg29411,⟨sg29407,⟨sg29405,⟨sg29404,True.intro,True.intro⟩,⟨sg29406,True.intro,True.intro⟩⟩,⟨sg29409,⟨sg29408,True.intro,True.intro⟩,⟨sg29410,True.intro,True.intro⟩⟩⟩,⟨sg29415,⟨sg29413,⟨sg29412,True.intro,True.intro⟩,⟨sg29414,True.intro,True.intro⟩⟩,⟨sg29417,⟨sg29416,True.intro,True.intro⟩,⟨sg29418,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_449All : degreeTree43_449.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29387,degreeTree43_447All,degreeTree43_448All⟩

lemma degreeTree43_450All : degreeTree43_450.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29435,⟨sg29427,⟨sg29423,⟨sg29421,⟨sg29420,True.intro,True.intro⟩,⟨sg29422,True.intro,True.intro⟩⟩,⟨sg29425,⟨sg29424,True.intro,True.intro⟩,⟨sg29426,True.intro,True.intro⟩⟩⟩,⟨sg29431,⟨sg29429,⟨sg29428,True.intro,True.intro⟩,⟨sg29430,True.intro,True.intro⟩⟩,⟨sg29433,⟨sg29432,True.intro,True.intro⟩,⟨sg29434,True.intro,True.intro⟩⟩⟩⟩,⟨sg29443,⟨sg29439,⟨sg29437,⟨sg29436,True.intro,True.intro⟩,⟨sg29438,True.intro,True.intro⟩⟩,⟨sg29441,⟨sg29440,True.intro,True.intro⟩,⟨sg29442,True.intro,True.intro⟩⟩⟩,⟨sg29447,⟨sg29445,⟨sg29444,True.intro,True.intro⟩,⟨sg29446,True.intro,True.intro⟩⟩,⟨sg29449,⟨sg29448,True.intro,True.intro⟩,⟨sg29450,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_451All : degreeTree43_451.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29467,⟨sg29459,⟨sg29455,⟨sg29453,⟨sg29452,True.intro,True.intro⟩,⟨sg29454,True.intro,True.intro⟩⟩,⟨sg29457,⟨sg29456,True.intro,True.intro⟩,⟨sg29458,True.intro,True.intro⟩⟩⟩,⟨sg29463,⟨sg29461,⟨sg29460,True.intro,True.intro⟩,⟨sg29462,True.intro,True.intro⟩⟩,⟨sg29465,⟨sg29464,True.intro,True.intro⟩,⟨sg29466,True.intro,True.intro⟩⟩⟩⟩,⟨sg29475,⟨sg29471,⟨sg29469,⟨sg29468,True.intro,True.intro⟩,⟨sg29470,True.intro,True.intro⟩⟩,⟨sg29473,⟨sg29472,True.intro,True.intro⟩,⟨sg29474,True.intro,True.intro⟩⟩⟩,⟨sg29479,⟨sg29477,⟨sg29476,True.intro,True.intro⟩,⟨sg29478,True.intro,True.intro⟩⟩,⟨sg29481,⟨sg29480,True.intro,True.intro⟩,⟨sg29482,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_452All : degreeTree43_452.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29451,degreeTree43_450All,degreeTree43_451All⟩

lemma degreeTree43_453All : degreeTree43_453.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29419,degreeTree43_449All,degreeTree43_452All⟩

lemma degreeTree43_454All : degreeTree43_454.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29492,⟨sg29488,⟨sg29486,⟨sg29485,⟨sg29484,True.intro,True.intro⟩,True.intro⟩,⟨sg29487,True.intro,True.intro⟩⟩,⟨sg29490,⟨sg29489,True.intro,True.intro⟩,⟨sg29491,True.intro,True.intro⟩⟩⟩,⟨sg29496,⟨sg29494,⟨sg29493,True.intro,True.intro⟩,⟨sg29495,True.intro,True.intro⟩⟩,⟨sg29498,⟨sg29497,True.intro,True.intro⟩,⟨sg29499,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_455All : degreeTree43_455.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29508,⟨sg29504,⟨sg29502,⟨sg29501,True.intro,True.intro⟩,⟨sg29503,True.intro,True.intro⟩⟩,⟨sg29506,⟨sg29505,True.intro,True.intro⟩,⟨sg29507,True.intro,True.intro⟩⟩⟩,⟨sg29512,⟨sg29510,⟨sg29509,True.intro,True.intro⟩,⟨sg29511,True.intro,True.intro⟩⟩,⟨sg29514,⟨sg29513,True.intro,True.intro⟩,⟨sg29515,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_456All : degreeTree43_456.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29500,degreeTree43_454All,degreeTree43_455All⟩

lemma degreeTree43_457All : degreeTree43_457.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29532,⟨sg29524,⟨sg29520,⟨sg29518,⟨sg29517,True.intro,True.intro⟩,⟨sg29519,True.intro,True.intro⟩⟩,⟨sg29522,⟨sg29521,True.intro,True.intro⟩,⟨sg29523,True.intro,True.intro⟩⟩⟩,⟨sg29528,⟨sg29526,⟨sg29525,True.intro,True.intro⟩,⟨sg29527,True.intro,True.intro⟩⟩,⟨sg29530,⟨sg29529,True.intro,True.intro⟩,⟨sg29531,True.intro,True.intro⟩⟩⟩⟩,⟨sg29540,⟨sg29536,⟨sg29534,⟨sg29533,True.intro,True.intro⟩,⟨sg29535,True.intro,True.intro⟩⟩,⟨sg29538,⟨sg29537,True.intro,True.intro⟩,⟨sg29539,True.intro,True.intro⟩⟩⟩,⟨sg29544,⟨sg29542,⟨sg29541,True.intro,True.intro⟩,⟨sg29543,True.intro,True.intro⟩⟩,⟨sg29546,⟨sg29545,True.intro,True.intro⟩,⟨sg29547,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_458All : degreeTree43_458.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29516,degreeTree43_456All,degreeTree43_457All⟩

lemma degreeTree43_459All : degreeTree43_459.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29564,⟨sg29556,⟨sg29552,⟨sg29550,⟨sg29549,True.intro,True.intro⟩,⟨sg29551,True.intro,True.intro⟩⟩,⟨sg29554,⟨sg29553,True.intro,True.intro⟩,⟨sg29555,True.intro,True.intro⟩⟩⟩,⟨sg29560,⟨sg29558,⟨sg29557,True.intro,True.intro⟩,⟨sg29559,True.intro,True.intro⟩⟩,⟨sg29562,⟨sg29561,True.intro,True.intro⟩,⟨sg29563,True.intro,True.intro⟩⟩⟩⟩,⟨sg29572,⟨sg29568,⟨sg29566,⟨sg29565,True.intro,True.intro⟩,⟨sg29567,True.intro,True.intro⟩⟩,⟨sg29570,⟨sg29569,True.intro,True.intro⟩,⟨sg29571,True.intro,True.intro⟩⟩⟩,⟨sg29576,⟨sg29574,⟨sg29573,True.intro,True.intro⟩,⟨sg29575,True.intro,True.intro⟩⟩,⟨sg29578,⟨sg29577,True.intro,True.intro⟩,⟨sg29579,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_460All : degreeTree43_460.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29596,⟨sg29588,⟨sg29584,⟨sg29582,⟨sg29581,True.intro,True.intro⟩,⟨sg29583,True.intro,True.intro⟩⟩,⟨sg29586,⟨sg29585,True.intro,True.intro⟩,⟨sg29587,True.intro,True.intro⟩⟩⟩,⟨sg29592,⟨sg29590,⟨sg29589,True.intro,True.intro⟩,⟨sg29591,True.intro,True.intro⟩⟩,⟨sg29594,⟨sg29593,True.intro,True.intro⟩,⟨sg29595,True.intro,True.intro⟩⟩⟩⟩,⟨sg29604,⟨sg29600,⟨sg29598,⟨sg29597,True.intro,True.intro⟩,⟨sg29599,True.intro,True.intro⟩⟩,⟨sg29602,⟨sg29601,True.intro,True.intro⟩,⟨sg29603,True.intro,True.intro⟩⟩⟩,⟨sg29608,⟨sg29606,⟨sg29605,True.intro,True.intro⟩,⟨sg29607,True.intro,True.intro⟩⟩,⟨sg29610,⟨sg29609,True.intro,True.intro⟩,⟨sg29611,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_461All : degreeTree43_461.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29580,degreeTree43_459All,degreeTree43_460All⟩

lemma degreeTree43_462All : degreeTree43_462.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29548,degreeTree43_458All,degreeTree43_461All⟩

lemma degreeTree43_463All : degreeTree43_463.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29483,degreeTree43_453All,degreeTree43_462All⟩

lemma degreeTree43_464All : degreeTree43_464.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29621,⟨sg29617,⟨sg29615,⟨sg29614,⟨sg29613,True.intro,True.intro⟩,True.intro⟩,⟨sg29616,True.intro,True.intro⟩⟩,⟨sg29619,⟨sg29618,True.intro,True.intro⟩,⟨sg29620,True.intro,True.intro⟩⟩⟩,⟨sg29625,⟨sg29623,⟨sg29622,True.intro,True.intro⟩,⟨sg29624,True.intro,True.intro⟩⟩,⟨sg29627,⟨sg29626,True.intro,True.intro⟩,⟨sg29628,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_465All : degreeTree43_465.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29637,⟨sg29633,⟨sg29631,⟨sg29630,True.intro,True.intro⟩,⟨sg29632,True.intro,True.intro⟩⟩,⟨sg29635,⟨sg29634,True.intro,True.intro⟩,⟨sg29636,True.intro,True.intro⟩⟩⟩,⟨sg29641,⟨sg29639,⟨sg29638,True.intro,True.intro⟩,⟨sg29640,True.intro,True.intro⟩⟩,⟨sg29643,⟨sg29642,True.intro,True.intro⟩,⟨sg29644,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_466All : degreeTree43_466.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29629,degreeTree43_464All,degreeTree43_465All⟩

lemma degreeTree43_467All : degreeTree43_467.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29661,⟨sg29653,⟨sg29649,⟨sg29647,⟨sg29646,True.intro,True.intro⟩,⟨sg29648,True.intro,True.intro⟩⟩,⟨sg29651,⟨sg29650,True.intro,True.intro⟩,⟨sg29652,True.intro,True.intro⟩⟩⟩,⟨sg29657,⟨sg29655,⟨sg29654,True.intro,True.intro⟩,⟨sg29656,True.intro,True.intro⟩⟩,⟨sg29659,⟨sg29658,True.intro,True.intro⟩,⟨sg29660,True.intro,True.intro⟩⟩⟩⟩,⟨sg29669,⟨sg29665,⟨sg29663,⟨sg29662,True.intro,True.intro⟩,⟨sg29664,True.intro,True.intro⟩⟩,⟨sg29667,⟨sg29666,True.intro,True.intro⟩,⟨sg29668,True.intro,True.intro⟩⟩⟩,⟨sg29673,⟨sg29671,⟨sg29670,True.intro,True.intro⟩,⟨sg29672,True.intro,True.intro⟩⟩,⟨sg29675,⟨sg29674,True.intro,True.intro⟩,⟨sg29676,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_468All : degreeTree43_468.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29645,degreeTree43_466All,degreeTree43_467All⟩

lemma degreeTree43_469All : degreeTree43_469.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29693,⟨sg29685,⟨sg29681,⟨sg29679,⟨sg29678,True.intro,True.intro⟩,⟨sg29680,True.intro,True.intro⟩⟩,⟨sg29683,⟨sg29682,True.intro,True.intro⟩,⟨sg29684,True.intro,True.intro⟩⟩⟩,⟨sg29689,⟨sg29687,⟨sg29686,True.intro,True.intro⟩,⟨sg29688,True.intro,True.intro⟩⟩,⟨sg29691,⟨sg29690,True.intro,True.intro⟩,⟨sg29692,True.intro,True.intro⟩⟩⟩⟩,⟨sg29701,⟨sg29697,⟨sg29695,⟨sg29694,True.intro,True.intro⟩,⟨sg29696,True.intro,True.intro⟩⟩,⟨sg29699,⟨sg29698,True.intro,True.intro⟩,⟨sg29700,True.intro,True.intro⟩⟩⟩,⟨sg29705,⟨sg29703,⟨sg29702,True.intro,True.intro⟩,⟨sg29704,True.intro,True.intro⟩⟩,⟨sg29707,⟨sg29706,True.intro,True.intro⟩,⟨sg29708,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_470All : degreeTree43_470.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29725,⟨sg29717,⟨sg29713,⟨sg29711,⟨sg29710,True.intro,True.intro⟩,⟨sg29712,True.intro,True.intro⟩⟩,⟨sg29715,⟨sg29714,True.intro,True.intro⟩,⟨sg29716,True.intro,True.intro⟩⟩⟩,⟨sg29721,⟨sg29719,⟨sg29718,True.intro,True.intro⟩,⟨sg29720,True.intro,True.intro⟩⟩,⟨sg29723,⟨sg29722,True.intro,True.intro⟩,⟨sg29724,True.intro,True.intro⟩⟩⟩⟩,⟨sg29733,⟨sg29729,⟨sg29727,⟨sg29726,True.intro,True.intro⟩,⟨sg29728,True.intro,True.intro⟩⟩,⟨sg29731,⟨sg29730,True.intro,True.intro⟩,⟨sg29732,True.intro,True.intro⟩⟩⟩,⟨sg29737,⟨sg29735,⟨sg29734,True.intro,True.intro⟩,⟨sg29736,True.intro,True.intro⟩⟩,⟨sg29739,⟨sg29738,True.intro,True.intro⟩,⟨sg29740,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_471All : degreeTree43_471.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29709,degreeTree43_469All,degreeTree43_470All⟩

lemma degreeTree43_472All : degreeTree43_472.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29677,degreeTree43_468All,degreeTree43_471All⟩

lemma degreeTree43_473All : degreeTree43_473.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29750,⟨sg29746,⟨sg29744,⟨sg29743,⟨sg29742,True.intro,True.intro⟩,True.intro⟩,⟨sg29745,True.intro,True.intro⟩⟩,⟨sg29748,⟨sg29747,True.intro,True.intro⟩,⟨sg29749,True.intro,True.intro⟩⟩⟩,⟨sg29754,⟨sg29752,⟨sg29751,True.intro,True.intro⟩,⟨sg29753,True.intro,True.intro⟩⟩,⟨sg29756,⟨sg29755,True.intro,True.intro⟩,⟨sg29757,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_474All : degreeTree43_474.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29766,⟨sg29762,⟨sg29760,⟨sg29759,True.intro,True.intro⟩,⟨sg29761,True.intro,True.intro⟩⟩,⟨sg29764,⟨sg29763,True.intro,True.intro⟩,⟨sg29765,True.intro,True.intro⟩⟩⟩,⟨sg29770,⟨sg29768,⟨sg29767,True.intro,True.intro⟩,⟨sg29769,True.intro,True.intro⟩⟩,⟨sg29772,⟨sg29771,True.intro,True.intro⟩,⟨sg29773,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_475All : degreeTree43_475.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29758,degreeTree43_473All,degreeTree43_474All⟩

lemma degreeTree43_476All : degreeTree43_476.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29790,⟨sg29782,⟨sg29778,⟨sg29776,⟨sg29775,True.intro,True.intro⟩,⟨sg29777,True.intro,True.intro⟩⟩,⟨sg29780,⟨sg29779,True.intro,True.intro⟩,⟨sg29781,True.intro,True.intro⟩⟩⟩,⟨sg29786,⟨sg29784,⟨sg29783,True.intro,True.intro⟩,⟨sg29785,True.intro,True.intro⟩⟩,⟨sg29788,⟨sg29787,True.intro,True.intro⟩,⟨sg29789,True.intro,True.intro⟩⟩⟩⟩,⟨sg29798,⟨sg29794,⟨sg29792,⟨sg29791,True.intro,True.intro⟩,⟨sg29793,True.intro,True.intro⟩⟩,⟨sg29796,⟨sg29795,True.intro,True.intro⟩,⟨sg29797,True.intro,True.intro⟩⟩⟩,⟨sg29802,⟨sg29800,⟨sg29799,True.intro,True.intro⟩,⟨sg29801,True.intro,True.intro⟩⟩,⟨sg29804,⟨sg29803,True.intro,True.intro⟩,⟨sg29805,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_477All : degreeTree43_477.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29774,degreeTree43_475All,degreeTree43_476All⟩

lemma degreeTree43_478All : degreeTree43_478.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29822,⟨sg29814,⟨sg29810,⟨sg29808,⟨sg29807,True.intro,True.intro⟩,⟨sg29809,True.intro,True.intro⟩⟩,⟨sg29812,⟨sg29811,True.intro,True.intro⟩,⟨sg29813,True.intro,True.intro⟩⟩⟩,⟨sg29818,⟨sg29816,⟨sg29815,True.intro,True.intro⟩,⟨sg29817,True.intro,True.intro⟩⟩,⟨sg29820,⟨sg29819,True.intro,True.intro⟩,⟨sg29821,True.intro,True.intro⟩⟩⟩⟩,⟨sg29830,⟨sg29826,⟨sg29824,⟨sg29823,True.intro,True.intro⟩,⟨sg29825,True.intro,True.intro⟩⟩,⟨sg29828,⟨sg29827,True.intro,True.intro⟩,⟨sg29829,True.intro,True.intro⟩⟩⟩,⟨sg29834,⟨sg29832,⟨sg29831,True.intro,True.intro⟩,⟨sg29833,True.intro,True.intro⟩⟩,⟨sg29836,⟨sg29835,True.intro,True.intro⟩,⟨sg29837,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_479All : degreeTree43_479.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29854,⟨sg29846,⟨sg29842,⟨sg29840,⟨sg29839,True.intro,True.intro⟩,⟨sg29841,True.intro,True.intro⟩⟩,⟨sg29844,⟨sg29843,True.intro,True.intro⟩,⟨sg29845,True.intro,True.intro⟩⟩⟩,⟨sg29850,⟨sg29848,⟨sg29847,True.intro,True.intro⟩,⟨sg29849,True.intro,True.intro⟩⟩,⟨sg29852,⟨sg29851,True.intro,True.intro⟩,⟨sg29853,True.intro,True.intro⟩⟩⟩⟩,⟨sg29862,⟨sg29858,⟨sg29856,⟨sg29855,True.intro,True.intro⟩,⟨sg29857,True.intro,True.intro⟩⟩,⟨sg29860,⟨sg29859,True.intro,True.intro⟩,⟨sg29861,True.intro,True.intro⟩⟩⟩,⟨sg29866,⟨sg29864,⟨sg29863,True.intro,True.intro⟩,⟨sg29865,True.intro,True.intro⟩⟩,⟨sg29868,⟨sg29867,True.intro,True.intro⟩,⟨sg29869,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_480All : degreeTree43_480.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29838,degreeTree43_478All,degreeTree43_479All⟩

lemma degreeTree43_481All : degreeTree43_481.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29806,degreeTree43_477All,degreeTree43_480All⟩

lemma degreeTree43_482All : degreeTree43_482.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29741,degreeTree43_472All,degreeTree43_481All⟩

lemma degreeTree43_483All : degreeTree43_483.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29612,degreeTree43_463All,degreeTree43_482All⟩

lemma degreeTree43_484All : degreeTree43_484.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29354,degreeTree43_444All,degreeTree43_483All⟩

lemma degreeTree43_485All : degreeTree43_485.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg28838,degreeTree43_405All,degreeTree43_484All⟩

lemma degreeTree43_486All : degreeTree43_486.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29879,⟨sg29875,⟨sg29873,⟨sg29872,⟨sg29871,True.intro,True.intro⟩,True.intro⟩,⟨sg29874,True.intro,True.intro⟩⟩,⟨sg29877,⟨sg29876,True.intro,True.intro⟩,⟨sg29878,True.intro,True.intro⟩⟩⟩,⟨sg29883,⟨sg29881,⟨sg29880,True.intro,True.intro⟩,⟨sg29882,True.intro,True.intro⟩⟩,⟨sg29885,⟨sg29884,True.intro,True.intro⟩,⟨sg29886,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_487All : degreeTree43_487.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29895,⟨sg29891,⟨sg29889,⟨sg29888,True.intro,True.intro⟩,⟨sg29890,True.intro,True.intro⟩⟩,⟨sg29893,⟨sg29892,True.intro,True.intro⟩,⟨sg29894,True.intro,True.intro⟩⟩⟩,⟨sg29899,⟨sg29897,⟨sg29896,True.intro,True.intro⟩,⟨sg29898,True.intro,True.intro⟩⟩,⟨sg29901,⟨sg29900,True.intro,True.intro⟩,⟨sg29902,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_488All : degreeTree43_488.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29887,degreeTree43_486All,degreeTree43_487All⟩

lemma degreeTree43_489All : degreeTree43_489.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29919,⟨sg29911,⟨sg29907,⟨sg29905,⟨sg29904,True.intro,True.intro⟩,⟨sg29906,True.intro,True.intro⟩⟩,⟨sg29909,⟨sg29908,True.intro,True.intro⟩,⟨sg29910,True.intro,True.intro⟩⟩⟩,⟨sg29915,⟨sg29913,⟨sg29912,True.intro,True.intro⟩,⟨sg29914,True.intro,True.intro⟩⟩,⟨sg29917,⟨sg29916,True.intro,True.intro⟩,⟨sg29918,True.intro,True.intro⟩⟩⟩⟩,⟨sg29927,⟨sg29923,⟨sg29921,⟨sg29920,True.intro,True.intro⟩,⟨sg29922,True.intro,True.intro⟩⟩,⟨sg29925,⟨sg29924,True.intro,True.intro⟩,⟨sg29926,True.intro,True.intro⟩⟩⟩,⟨sg29931,⟨sg29929,⟨sg29928,True.intro,True.intro⟩,⟨sg29930,True.intro,True.intro⟩⟩,⟨sg29933,⟨sg29932,True.intro,True.intro⟩,⟨sg29934,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_490All : degreeTree43_490.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29903,degreeTree43_488All,degreeTree43_489All⟩

lemma degreeTree43_491All : degreeTree43_491.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29944,⟨sg29940,⟨sg29938,⟨sg29937,⟨sg29936,True.intro,True.intro⟩,True.intro⟩,⟨sg29939,True.intro,True.intro⟩⟩,⟨sg29942,⟨sg29941,True.intro,True.intro⟩,⟨sg29943,True.intro,True.intro⟩⟩⟩,⟨sg29948,⟨sg29946,⟨sg29945,True.intro,True.intro⟩,⟨sg29947,True.intro,True.intro⟩⟩,⟨sg29950,⟨sg29949,True.intro,True.intro⟩,⟨sg29951,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_492All : degreeTree43_492.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29960,⟨sg29956,⟨sg29954,⟨sg29953,True.intro,True.intro⟩,⟨sg29955,True.intro,True.intro⟩⟩,⟨sg29958,⟨sg29957,True.intro,True.intro⟩,⟨sg29959,True.intro,True.intro⟩⟩⟩,⟨sg29964,⟨sg29962,⟨sg29961,True.intro,True.intro⟩,⟨sg29963,True.intro,True.intro⟩⟩,⟨sg29966,⟨sg29965,True.intro,True.intro⟩,⟨sg29967,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_493All : degreeTree43_493.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29952,degreeTree43_491All,degreeTree43_492All⟩

lemma degreeTree43_494All : degreeTree43_494.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29984,⟨sg29976,⟨sg29972,⟨sg29970,⟨sg29969,True.intro,True.intro⟩,⟨sg29971,True.intro,True.intro⟩⟩,⟨sg29974,⟨sg29973,True.intro,True.intro⟩,⟨sg29975,True.intro,True.intro⟩⟩⟩,⟨sg29980,⟨sg29978,⟨sg29977,True.intro,True.intro⟩,⟨sg29979,True.intro,True.intro⟩⟩,⟨sg29982,⟨sg29981,True.intro,True.intro⟩,⟨sg29983,True.intro,True.intro⟩⟩⟩⟩,⟨sg29992,⟨sg29988,⟨sg29986,⟨sg29985,True.intro,True.intro⟩,⟨sg29987,True.intro,True.intro⟩⟩,⟨sg29990,⟨sg29989,True.intro,True.intro⟩,⟨sg29991,True.intro,True.intro⟩⟩⟩,⟨sg29996,⟨sg29994,⟨sg29993,True.intro,True.intro⟩,⟨sg29995,True.intro,True.intro⟩⟩,⟨sg29998,⟨sg29997,True.intro,True.intro⟩,⟨sg29999,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_495All : degreeTree43_495.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29968,degreeTree43_493All,degreeTree43_494All⟩

lemma degreeTree43_496All : degreeTree43_496.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29935,degreeTree43_490All,degreeTree43_495All⟩

lemma degreeTree43_497All : degreeTree43_497.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30009,⟨sg30005,⟨sg30003,⟨sg30002,⟨sg30001,True.intro,True.intro⟩,True.intro⟩,⟨sg30004,True.intro,True.intro⟩⟩,⟨sg30007,⟨sg30006,True.intro,True.intro⟩,⟨sg30008,True.intro,True.intro⟩⟩⟩,⟨sg30013,⟨sg30011,⟨sg30010,True.intro,True.intro⟩,⟨sg30012,True.intro,True.intro⟩⟩,⟨sg30015,⟨sg30014,True.intro,True.intro⟩,⟨sg30016,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_498All : degreeTree43_498.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30025,⟨sg30021,⟨sg30019,⟨sg30018,True.intro,True.intro⟩,⟨sg30020,True.intro,True.intro⟩⟩,⟨sg30023,⟨sg30022,True.intro,True.intro⟩,⟨sg30024,True.intro,True.intro⟩⟩⟩,⟨sg30029,⟨sg30027,⟨sg30026,True.intro,True.intro⟩,⟨sg30028,True.intro,True.intro⟩⟩,⟨sg30031,⟨sg30030,True.intro,True.intro⟩,⟨sg30032,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_499All : degreeTree43_499.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30017,degreeTree43_497All,degreeTree43_498All⟩

lemma degreeTree43_500All : degreeTree43_500.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30049,⟨sg30041,⟨sg30037,⟨sg30035,⟨sg30034,True.intro,True.intro⟩,⟨sg30036,True.intro,True.intro⟩⟩,⟨sg30039,⟨sg30038,True.intro,True.intro⟩,⟨sg30040,True.intro,True.intro⟩⟩⟩,⟨sg30045,⟨sg30043,⟨sg30042,True.intro,True.intro⟩,⟨sg30044,True.intro,True.intro⟩⟩,⟨sg30047,⟨sg30046,True.intro,True.intro⟩,⟨sg30048,True.intro,True.intro⟩⟩⟩⟩,⟨sg30057,⟨sg30053,⟨sg30051,⟨sg30050,True.intro,True.intro⟩,⟨sg30052,True.intro,True.intro⟩⟩,⟨sg30055,⟨sg30054,True.intro,True.intro⟩,⟨sg30056,True.intro,True.intro⟩⟩⟩,⟨sg30061,⟨sg30059,⟨sg30058,True.intro,True.intro⟩,⟨sg30060,True.intro,True.intro⟩⟩,⟨sg30063,⟨sg30062,True.intro,True.intro⟩,⟨sg30064,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_501All : degreeTree43_501.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30033,degreeTree43_499All,degreeTree43_500All⟩

lemma degreeTree43_502All : degreeTree43_502.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30081,⟨sg30073,⟨sg30069,⟨sg30067,⟨sg30066,True.intro,True.intro⟩,⟨sg30068,True.intro,True.intro⟩⟩,⟨sg30071,⟨sg30070,True.intro,True.intro⟩,⟨sg30072,True.intro,True.intro⟩⟩⟩,⟨sg30077,⟨sg30075,⟨sg30074,True.intro,True.intro⟩,⟨sg30076,True.intro,True.intro⟩⟩,⟨sg30079,⟨sg30078,True.intro,True.intro⟩,⟨sg30080,True.intro,True.intro⟩⟩⟩⟩,⟨sg30089,⟨sg30085,⟨sg30083,⟨sg30082,True.intro,True.intro⟩,⟨sg30084,True.intro,True.intro⟩⟩,⟨sg30087,⟨sg30086,True.intro,True.intro⟩,⟨sg30088,True.intro,True.intro⟩⟩⟩,⟨sg30093,⟨sg30091,⟨sg30090,True.intro,True.intro⟩,⟨sg30092,True.intro,True.intro⟩⟩,⟨sg30095,⟨sg30094,True.intro,True.intro⟩,⟨sg30096,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_503All : degreeTree43_503.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30113,⟨sg30105,⟨sg30101,⟨sg30099,⟨sg30098,True.intro,True.intro⟩,⟨sg30100,True.intro,True.intro⟩⟩,⟨sg30103,⟨sg30102,True.intro,True.intro⟩,⟨sg30104,True.intro,True.intro⟩⟩⟩,⟨sg30109,⟨sg30107,⟨sg30106,True.intro,True.intro⟩,⟨sg30108,True.intro,True.intro⟩⟩,⟨sg30111,⟨sg30110,True.intro,True.intro⟩,⟨sg30112,True.intro,True.intro⟩⟩⟩⟩,⟨sg30121,⟨sg30117,⟨sg30115,⟨sg30114,True.intro,True.intro⟩,⟨sg30116,True.intro,True.intro⟩⟩,⟨sg30119,⟨sg30118,True.intro,True.intro⟩,⟨sg30120,True.intro,True.intro⟩⟩⟩,⟨sg30125,⟨sg30123,⟨sg30122,True.intro,True.intro⟩,⟨sg30124,True.intro,True.intro⟩⟩,⟨sg30127,⟨sg30126,True.intro,True.intro⟩,⟨sg30128,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_504All : degreeTree43_504.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30097,degreeTree43_502All,degreeTree43_503All⟩

lemma degreeTree43_505All : degreeTree43_505.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30065,degreeTree43_501All,degreeTree43_504All⟩

lemma degreeTree43_506All : degreeTree43_506.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30000,degreeTree43_496All,degreeTree43_505All⟩

lemma degreeTree43_507All : degreeTree43_507.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30138,⟨sg30134,⟨sg30132,⟨sg30131,⟨sg30130,True.intro,True.intro⟩,True.intro⟩,⟨sg30133,True.intro,True.intro⟩⟩,⟨sg30136,⟨sg30135,True.intro,True.intro⟩,⟨sg30137,True.intro,True.intro⟩⟩⟩,⟨sg30142,⟨sg30140,⟨sg30139,True.intro,True.intro⟩,⟨sg30141,True.intro,True.intro⟩⟩,⟨sg30144,⟨sg30143,True.intro,True.intro⟩,⟨sg30145,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_508All : degreeTree43_508.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30154,⟨sg30150,⟨sg30148,⟨sg30147,True.intro,True.intro⟩,⟨sg30149,True.intro,True.intro⟩⟩,⟨sg30152,⟨sg30151,True.intro,True.intro⟩,⟨sg30153,True.intro,True.intro⟩⟩⟩,⟨sg30158,⟨sg30156,⟨sg30155,True.intro,True.intro⟩,⟨sg30157,True.intro,True.intro⟩⟩,⟨sg30160,⟨sg30159,True.intro,True.intro⟩,⟨sg30161,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_509All : degreeTree43_509.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30146,degreeTree43_507All,degreeTree43_508All⟩

lemma degreeTree43_510All : degreeTree43_510.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30178,⟨sg30170,⟨sg30166,⟨sg30164,⟨sg30163,True.intro,True.intro⟩,⟨sg30165,True.intro,True.intro⟩⟩,⟨sg30168,⟨sg30167,True.intro,True.intro⟩,⟨sg30169,True.intro,True.intro⟩⟩⟩,⟨sg30174,⟨sg30172,⟨sg30171,True.intro,True.intro⟩,⟨sg30173,True.intro,True.intro⟩⟩,⟨sg30176,⟨sg30175,True.intro,True.intro⟩,⟨sg30177,True.intro,True.intro⟩⟩⟩⟩,⟨sg30186,⟨sg30182,⟨sg30180,⟨sg30179,True.intro,True.intro⟩,⟨sg30181,True.intro,True.intro⟩⟩,⟨sg30184,⟨sg30183,True.intro,True.intro⟩,⟨sg30185,True.intro,True.intro⟩⟩⟩,⟨sg30190,⟨sg30188,⟨sg30187,True.intro,True.intro⟩,⟨sg30189,True.intro,True.intro⟩⟩,⟨sg30192,⟨sg30191,True.intro,True.intro⟩,⟨sg30193,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_511All : degreeTree43_511.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30162,degreeTree43_509All,degreeTree43_510All⟩

lemma degreeTree43_512All : degreeTree43_512.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30210,⟨sg30202,⟨sg30198,⟨sg30196,⟨sg30195,True.intro,True.intro⟩,⟨sg30197,True.intro,True.intro⟩⟩,⟨sg30200,⟨sg30199,True.intro,True.intro⟩,⟨sg30201,True.intro,True.intro⟩⟩⟩,⟨sg30206,⟨sg30204,⟨sg30203,True.intro,True.intro⟩,⟨sg30205,True.intro,True.intro⟩⟩,⟨sg30208,⟨sg30207,True.intro,True.intro⟩,⟨sg30209,True.intro,True.intro⟩⟩⟩⟩,⟨sg30218,⟨sg30214,⟨sg30212,⟨sg30211,True.intro,True.intro⟩,⟨sg30213,True.intro,True.intro⟩⟩,⟨sg30216,⟨sg30215,True.intro,True.intro⟩,⟨sg30217,True.intro,True.intro⟩⟩⟩,⟨sg30222,⟨sg30220,⟨sg30219,True.intro,True.intro⟩,⟨sg30221,True.intro,True.intro⟩⟩,⟨sg30224,⟨sg30223,True.intro,True.intro⟩,⟨sg30225,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_513All : degreeTree43_513.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30242,⟨sg30234,⟨sg30230,⟨sg30228,⟨sg30227,True.intro,True.intro⟩,⟨sg30229,True.intro,True.intro⟩⟩,⟨sg30232,⟨sg30231,True.intro,True.intro⟩,⟨sg30233,True.intro,True.intro⟩⟩⟩,⟨sg30238,⟨sg30236,⟨sg30235,True.intro,True.intro⟩,⟨sg30237,True.intro,True.intro⟩⟩,⟨sg30240,⟨sg30239,True.intro,True.intro⟩,⟨sg30241,True.intro,True.intro⟩⟩⟩⟩,⟨sg30250,⟨sg30246,⟨sg30244,⟨sg30243,True.intro,True.intro⟩,⟨sg30245,True.intro,True.intro⟩⟩,⟨sg30248,⟨sg30247,True.intro,True.intro⟩,⟨sg30249,True.intro,True.intro⟩⟩⟩,⟨sg30254,⟨sg30252,⟨sg30251,True.intro,True.intro⟩,⟨sg30253,True.intro,True.intro⟩⟩,⟨sg30256,⟨sg30255,True.intro,True.intro⟩,⟨sg30257,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_514All : degreeTree43_514.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30226,degreeTree43_512All,degreeTree43_513All⟩

lemma degreeTree43_515All : degreeTree43_515.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30194,degreeTree43_511All,degreeTree43_514All⟩

lemma degreeTree43_516All : degreeTree43_516.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30267,⟨sg30263,⟨sg30261,⟨sg30260,⟨sg30259,True.intro,True.intro⟩,True.intro⟩,⟨sg30262,True.intro,True.intro⟩⟩,⟨sg30265,⟨sg30264,True.intro,True.intro⟩,⟨sg30266,True.intro,True.intro⟩⟩⟩,⟨sg30271,⟨sg30269,⟨sg30268,True.intro,True.intro⟩,⟨sg30270,True.intro,True.intro⟩⟩,⟨sg30273,⟨sg30272,True.intro,True.intro⟩,⟨sg30274,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_517All : degreeTree43_517.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30283,⟨sg30279,⟨sg30277,⟨sg30276,True.intro,True.intro⟩,⟨sg30278,True.intro,True.intro⟩⟩,⟨sg30281,⟨sg30280,True.intro,True.intro⟩,⟨sg30282,True.intro,True.intro⟩⟩⟩,⟨sg30287,⟨sg30285,⟨sg30284,True.intro,True.intro⟩,⟨sg30286,True.intro,True.intro⟩⟩,⟨sg30289,⟨sg30288,True.intro,True.intro⟩,⟨sg30290,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_518All : degreeTree43_518.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30275,degreeTree43_516All,degreeTree43_517All⟩

lemma degreeTree43_519All : degreeTree43_519.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30307,⟨sg30299,⟨sg30295,⟨sg30293,⟨sg30292,True.intro,True.intro⟩,⟨sg30294,True.intro,True.intro⟩⟩,⟨sg30297,⟨sg30296,True.intro,True.intro⟩,⟨sg30298,True.intro,True.intro⟩⟩⟩,⟨sg30303,⟨sg30301,⟨sg30300,True.intro,True.intro⟩,⟨sg30302,True.intro,True.intro⟩⟩,⟨sg30305,⟨sg30304,True.intro,True.intro⟩,⟨sg30306,True.intro,True.intro⟩⟩⟩⟩,⟨sg30315,⟨sg30311,⟨sg30309,⟨sg30308,True.intro,True.intro⟩,⟨sg30310,True.intro,True.intro⟩⟩,⟨sg30313,⟨sg30312,True.intro,True.intro⟩,⟨sg30314,True.intro,True.intro⟩⟩⟩,⟨sg30319,⟨sg30317,⟨sg30316,True.intro,True.intro⟩,⟨sg30318,True.intro,True.intro⟩⟩,⟨sg30321,⟨sg30320,True.intro,True.intro⟩,⟨sg30322,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_520All : degreeTree43_520.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30291,degreeTree43_518All,degreeTree43_519All⟩

lemma degreeTree43_521All : degreeTree43_521.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30339,⟨sg30331,⟨sg30327,⟨sg30325,⟨sg30324,True.intro,True.intro⟩,⟨sg30326,True.intro,True.intro⟩⟩,⟨sg30329,⟨sg30328,True.intro,True.intro⟩,⟨sg30330,True.intro,True.intro⟩⟩⟩,⟨sg30335,⟨sg30333,⟨sg30332,True.intro,True.intro⟩,⟨sg30334,True.intro,True.intro⟩⟩,⟨sg30337,⟨sg30336,True.intro,True.intro⟩,⟨sg30338,True.intro,True.intro⟩⟩⟩⟩,⟨sg30347,⟨sg30343,⟨sg30341,⟨sg30340,True.intro,True.intro⟩,⟨sg30342,True.intro,True.intro⟩⟩,⟨sg30345,⟨sg30344,True.intro,True.intro⟩,⟨sg30346,True.intro,True.intro⟩⟩⟩,⟨sg30351,⟨sg30349,⟨sg30348,True.intro,True.intro⟩,⟨sg30350,True.intro,True.intro⟩⟩,⟨sg30353,⟨sg30352,True.intro,True.intro⟩,⟨sg30354,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_522All : degreeTree43_522.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30371,⟨sg30363,⟨sg30359,⟨sg30357,⟨sg30356,True.intro,True.intro⟩,⟨sg30358,True.intro,True.intro⟩⟩,⟨sg30361,⟨sg30360,True.intro,True.intro⟩,⟨sg30362,True.intro,True.intro⟩⟩⟩,⟨sg30367,⟨sg30365,⟨sg30364,True.intro,True.intro⟩,⟨sg30366,True.intro,True.intro⟩⟩,⟨sg30369,⟨sg30368,True.intro,True.intro⟩,⟨sg30370,True.intro,True.intro⟩⟩⟩⟩,⟨sg30379,⟨sg30375,⟨sg30373,⟨sg30372,True.intro,True.intro⟩,⟨sg30374,True.intro,True.intro⟩⟩,⟨sg30377,⟨sg30376,True.intro,True.intro⟩,⟨sg30378,True.intro,True.intro⟩⟩⟩,⟨sg30383,⟨sg30381,⟨sg30380,True.intro,True.intro⟩,⟨sg30382,True.intro,True.intro⟩⟩,⟨sg30385,⟨sg30384,True.intro,True.intro⟩,⟨sg30386,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_523All : degreeTree43_523.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30355,degreeTree43_521All,degreeTree43_522All⟩

lemma degreeTree43_524All : degreeTree43_524.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30323,degreeTree43_520All,degreeTree43_523All⟩

lemma degreeTree43_525All : degreeTree43_525.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30258,degreeTree43_515All,degreeTree43_524All⟩

lemma degreeTree43_526All : degreeTree43_526.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30129,degreeTree43_506All,degreeTree43_525All⟩

lemma degreeTree43_527All : degreeTree43_527.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30396,⟨sg30392,⟨sg30390,⟨sg30389,⟨sg30388,True.intro,True.intro⟩,True.intro⟩,⟨sg30391,True.intro,True.intro⟩⟩,⟨sg30394,⟨sg30393,True.intro,True.intro⟩,⟨sg30395,True.intro,True.intro⟩⟩⟩,⟨sg30400,⟨sg30398,⟨sg30397,True.intro,True.intro⟩,⟨sg30399,True.intro,True.intro⟩⟩,⟨sg30402,⟨sg30401,True.intro,True.intro⟩,⟨sg30403,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_528All : degreeTree43_528.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30412,⟨sg30408,⟨sg30406,⟨sg30405,True.intro,True.intro⟩,⟨sg30407,True.intro,True.intro⟩⟩,⟨sg30410,⟨sg30409,True.intro,True.intro⟩,⟨sg30411,True.intro,True.intro⟩⟩⟩,⟨sg30416,⟨sg30414,⟨sg30413,True.intro,True.intro⟩,⟨sg30415,True.intro,True.intro⟩⟩,⟨sg30418,⟨sg30417,True.intro,True.intro⟩,⟨sg30419,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_529All : degreeTree43_529.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30404,degreeTree43_527All,degreeTree43_528All⟩

lemma degreeTree43_530All : degreeTree43_530.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30436,⟨sg30428,⟨sg30424,⟨sg30422,⟨sg30421,True.intro,True.intro⟩,⟨sg30423,True.intro,True.intro⟩⟩,⟨sg30426,⟨sg30425,True.intro,True.intro⟩,⟨sg30427,True.intro,True.intro⟩⟩⟩,⟨sg30432,⟨sg30430,⟨sg30429,True.intro,True.intro⟩,⟨sg30431,True.intro,True.intro⟩⟩,⟨sg30434,⟨sg30433,True.intro,True.intro⟩,⟨sg30435,True.intro,True.intro⟩⟩⟩⟩,⟨sg30444,⟨sg30440,⟨sg30438,⟨sg30437,True.intro,True.intro⟩,⟨sg30439,True.intro,True.intro⟩⟩,⟨sg30442,⟨sg30441,True.intro,True.intro⟩,⟨sg30443,True.intro,True.intro⟩⟩⟩,⟨sg30448,⟨sg30446,⟨sg30445,True.intro,True.intro⟩,⟨sg30447,True.intro,True.intro⟩⟩,⟨sg30450,⟨sg30449,True.intro,True.intro⟩,⟨sg30451,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_531All : degreeTree43_531.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30420,degreeTree43_529All,degreeTree43_530All⟩

lemma degreeTree43_532All : degreeTree43_532.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30468,⟨sg30460,⟨sg30456,⟨sg30454,⟨sg30453,True.intro,True.intro⟩,⟨sg30455,True.intro,True.intro⟩⟩,⟨sg30458,⟨sg30457,True.intro,True.intro⟩,⟨sg30459,True.intro,True.intro⟩⟩⟩,⟨sg30464,⟨sg30462,⟨sg30461,True.intro,True.intro⟩,⟨sg30463,True.intro,True.intro⟩⟩,⟨sg30466,⟨sg30465,True.intro,True.intro⟩,⟨sg30467,True.intro,True.intro⟩⟩⟩⟩,⟨sg30476,⟨sg30472,⟨sg30470,⟨sg30469,True.intro,True.intro⟩,⟨sg30471,True.intro,True.intro⟩⟩,⟨sg30474,⟨sg30473,True.intro,True.intro⟩,⟨sg30475,True.intro,True.intro⟩⟩⟩,⟨sg30480,⟨sg30478,⟨sg30477,True.intro,True.intro⟩,⟨sg30479,True.intro,True.intro⟩⟩,⟨sg30482,⟨sg30481,True.intro,True.intro⟩,⟨sg30483,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_533All : degreeTree43_533.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30500,⟨sg30492,⟨sg30488,⟨sg30486,⟨sg30485,True.intro,True.intro⟩,⟨sg30487,True.intro,True.intro⟩⟩,⟨sg30490,⟨sg30489,True.intro,True.intro⟩,⟨sg30491,True.intro,True.intro⟩⟩⟩,⟨sg30496,⟨sg30494,⟨sg30493,True.intro,True.intro⟩,⟨sg30495,True.intro,True.intro⟩⟩,⟨sg30498,⟨sg30497,True.intro,True.intro⟩,⟨sg30499,True.intro,True.intro⟩⟩⟩⟩,⟨sg30508,⟨sg30504,⟨sg30502,⟨sg30501,True.intro,True.intro⟩,⟨sg30503,True.intro,True.intro⟩⟩,⟨sg30506,⟨sg30505,True.intro,True.intro⟩,⟨sg30507,True.intro,True.intro⟩⟩⟩,⟨sg30512,⟨sg30510,⟨sg30509,True.intro,True.intro⟩,⟨sg30511,True.intro,True.intro⟩⟩,⟨sg30514,⟨sg30513,True.intro,True.intro⟩,⟨sg30515,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_534All : degreeTree43_534.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30484,degreeTree43_532All,degreeTree43_533All⟩

lemma degreeTree43_535All : degreeTree43_535.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30452,degreeTree43_531All,degreeTree43_534All⟩

lemma degreeTree43_536All : degreeTree43_536.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30525,⟨sg30521,⟨sg30519,⟨sg30518,⟨sg30517,True.intro,True.intro⟩,True.intro⟩,⟨sg30520,True.intro,True.intro⟩⟩,⟨sg30523,⟨sg30522,True.intro,True.intro⟩,⟨sg30524,True.intro,True.intro⟩⟩⟩,⟨sg30529,⟨sg30527,⟨sg30526,True.intro,True.intro⟩,⟨sg30528,True.intro,True.intro⟩⟩,⟨sg30531,⟨sg30530,True.intro,True.intro⟩,⟨sg30532,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_537All : degreeTree43_537.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30541,⟨sg30537,⟨sg30535,⟨sg30534,True.intro,True.intro⟩,⟨sg30536,True.intro,True.intro⟩⟩,⟨sg30539,⟨sg30538,True.intro,True.intro⟩,⟨sg30540,True.intro,True.intro⟩⟩⟩,⟨sg30545,⟨sg30543,⟨sg30542,True.intro,True.intro⟩,⟨sg30544,True.intro,True.intro⟩⟩,⟨sg30547,⟨sg30546,True.intro,True.intro⟩,⟨sg30548,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_538All : degreeTree43_538.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30533,degreeTree43_536All,degreeTree43_537All⟩

lemma degreeTree43_539All : degreeTree43_539.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30565,⟨sg30557,⟨sg30553,⟨sg30551,⟨sg30550,True.intro,True.intro⟩,⟨sg30552,True.intro,True.intro⟩⟩,⟨sg30555,⟨sg30554,True.intro,True.intro⟩,⟨sg30556,True.intro,True.intro⟩⟩⟩,⟨sg30561,⟨sg30559,⟨sg30558,True.intro,True.intro⟩,⟨sg30560,True.intro,True.intro⟩⟩,⟨sg30563,⟨sg30562,True.intro,True.intro⟩,⟨sg30564,True.intro,True.intro⟩⟩⟩⟩,⟨sg30573,⟨sg30569,⟨sg30567,⟨sg30566,True.intro,True.intro⟩,⟨sg30568,True.intro,True.intro⟩⟩,⟨sg30571,⟨sg30570,True.intro,True.intro⟩,⟨sg30572,True.intro,True.intro⟩⟩⟩,⟨sg30577,⟨sg30575,⟨sg30574,True.intro,True.intro⟩,⟨sg30576,True.intro,True.intro⟩⟩,⟨sg30579,⟨sg30578,True.intro,True.intro⟩,⟨sg30580,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_540All : degreeTree43_540.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30549,degreeTree43_538All,degreeTree43_539All⟩

lemma degreeTree43_541All : degreeTree43_541.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30597,⟨sg30589,⟨sg30585,⟨sg30583,⟨sg30582,True.intro,True.intro⟩,⟨sg30584,True.intro,True.intro⟩⟩,⟨sg30587,⟨sg30586,True.intro,True.intro⟩,⟨sg30588,True.intro,True.intro⟩⟩⟩,⟨sg30593,⟨sg30591,⟨sg30590,True.intro,True.intro⟩,⟨sg30592,True.intro,True.intro⟩⟩,⟨sg30595,⟨sg30594,True.intro,True.intro⟩,⟨sg30596,True.intro,True.intro⟩⟩⟩⟩,⟨sg30605,⟨sg30601,⟨sg30599,⟨sg30598,True.intro,True.intro⟩,⟨sg30600,True.intro,True.intro⟩⟩,⟨sg30603,⟨sg30602,True.intro,True.intro⟩,⟨sg30604,True.intro,True.intro⟩⟩⟩,⟨sg30609,⟨sg30607,⟨sg30606,True.intro,True.intro⟩,⟨sg30608,True.intro,True.intro⟩⟩,⟨sg30611,⟨sg30610,True.intro,True.intro⟩,⟨sg30612,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_542All : degreeTree43_542.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30629,⟨sg30621,⟨sg30617,⟨sg30615,⟨sg30614,True.intro,True.intro⟩,⟨sg30616,True.intro,True.intro⟩⟩,⟨sg30619,⟨sg30618,True.intro,True.intro⟩,⟨sg30620,True.intro,True.intro⟩⟩⟩,⟨sg30625,⟨sg30623,⟨sg30622,True.intro,True.intro⟩,⟨sg30624,True.intro,True.intro⟩⟩,⟨sg30627,⟨sg30626,True.intro,True.intro⟩,⟨sg30628,True.intro,True.intro⟩⟩⟩⟩,⟨sg30637,⟨sg30633,⟨sg30631,⟨sg30630,True.intro,True.intro⟩,⟨sg30632,True.intro,True.intro⟩⟩,⟨sg30635,⟨sg30634,True.intro,True.intro⟩,⟨sg30636,True.intro,True.intro⟩⟩⟩,⟨sg30641,⟨sg30639,⟨sg30638,True.intro,True.intro⟩,⟨sg30640,True.intro,True.intro⟩⟩,⟨sg30643,⟨sg30642,True.intro,True.intro⟩,⟨sg30644,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_543All : degreeTree43_543.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30613,degreeTree43_541All,degreeTree43_542All⟩

lemma degreeTree43_544All : degreeTree43_544.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30581,degreeTree43_540All,degreeTree43_543All⟩

lemma degreeTree43_545All : degreeTree43_545.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30516,degreeTree43_535All,degreeTree43_544All⟩

lemma degreeTree43_546All : degreeTree43_546.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30654,⟨sg30650,⟨sg30648,⟨sg30647,⟨sg30646,True.intro,True.intro⟩,True.intro⟩,⟨sg30649,True.intro,True.intro⟩⟩,⟨sg30652,⟨sg30651,True.intro,True.intro⟩,⟨sg30653,True.intro,True.intro⟩⟩⟩,⟨sg30658,⟨sg30656,⟨sg30655,True.intro,True.intro⟩,⟨sg30657,True.intro,True.intro⟩⟩,⟨sg30660,⟨sg30659,True.intro,True.intro⟩,⟨sg30661,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_547All : degreeTree43_547.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30670,⟨sg30666,⟨sg30664,⟨sg30663,True.intro,True.intro⟩,⟨sg30665,True.intro,True.intro⟩⟩,⟨sg30668,⟨sg30667,True.intro,True.intro⟩,⟨sg30669,True.intro,True.intro⟩⟩⟩,⟨sg30674,⟨sg30672,⟨sg30671,True.intro,True.intro⟩,⟨sg30673,True.intro,True.intro⟩⟩,⟨sg30676,⟨sg30675,True.intro,True.intro⟩,⟨sg30677,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_548All : degreeTree43_548.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30662,degreeTree43_546All,degreeTree43_547All⟩

lemma degreeTree43_549All : degreeTree43_549.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30694,⟨sg30686,⟨sg30682,⟨sg30680,⟨sg30679,True.intro,True.intro⟩,⟨sg30681,True.intro,True.intro⟩⟩,⟨sg30684,⟨sg30683,True.intro,True.intro⟩,⟨sg30685,True.intro,True.intro⟩⟩⟩,⟨sg30690,⟨sg30688,⟨sg30687,True.intro,True.intro⟩,⟨sg30689,True.intro,True.intro⟩⟩,⟨sg30692,⟨sg30691,True.intro,True.intro⟩,⟨sg30693,True.intro,True.intro⟩⟩⟩⟩,⟨sg30702,⟨sg30698,⟨sg30696,⟨sg30695,True.intro,True.intro⟩,⟨sg30697,True.intro,True.intro⟩⟩,⟨sg30700,⟨sg30699,True.intro,True.intro⟩,⟨sg30701,True.intro,True.intro⟩⟩⟩,⟨sg30706,⟨sg30704,⟨sg30703,True.intro,True.intro⟩,⟨sg30705,True.intro,True.intro⟩⟩,⟨sg30708,⟨sg30707,True.intro,True.intro⟩,⟨sg30709,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_550All : degreeTree43_550.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30678,degreeTree43_548All,degreeTree43_549All⟩

lemma degreeTree43_551All : degreeTree43_551.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30726,⟨sg30718,⟨sg30714,⟨sg30712,⟨sg30711,True.intro,True.intro⟩,⟨sg30713,True.intro,True.intro⟩⟩,⟨sg30716,⟨sg30715,True.intro,True.intro⟩,⟨sg30717,True.intro,True.intro⟩⟩⟩,⟨sg30722,⟨sg30720,⟨sg30719,True.intro,True.intro⟩,⟨sg30721,True.intro,True.intro⟩⟩,⟨sg30724,⟨sg30723,True.intro,True.intro⟩,⟨sg30725,True.intro,True.intro⟩⟩⟩⟩,⟨sg30734,⟨sg30730,⟨sg30728,⟨sg30727,True.intro,True.intro⟩,⟨sg30729,True.intro,True.intro⟩⟩,⟨sg30732,⟨sg30731,True.intro,True.intro⟩,⟨sg30733,True.intro,True.intro⟩⟩⟩,⟨sg30738,⟨sg30736,⟨sg30735,True.intro,True.intro⟩,⟨sg30737,True.intro,True.intro⟩⟩,⟨sg30740,⟨sg30739,True.intro,True.intro⟩,⟨sg30741,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_552All : degreeTree43_552.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30758,⟨sg30750,⟨sg30746,⟨sg30744,⟨sg30743,True.intro,True.intro⟩,⟨sg30745,True.intro,True.intro⟩⟩,⟨sg30748,⟨sg30747,True.intro,True.intro⟩,⟨sg30749,True.intro,True.intro⟩⟩⟩,⟨sg30754,⟨sg30752,⟨sg30751,True.intro,True.intro⟩,⟨sg30753,True.intro,True.intro⟩⟩,⟨sg30756,⟨sg30755,True.intro,True.intro⟩,⟨sg30757,True.intro,True.intro⟩⟩⟩⟩,⟨sg30766,⟨sg30762,⟨sg30760,⟨sg30759,True.intro,True.intro⟩,⟨sg30761,True.intro,True.intro⟩⟩,⟨sg30764,⟨sg30763,True.intro,True.intro⟩,⟨sg30765,True.intro,True.intro⟩⟩⟩,⟨sg30770,⟨sg30768,⟨sg30767,True.intro,True.intro⟩,⟨sg30769,True.intro,True.intro⟩⟩,⟨sg30772,⟨sg30771,True.intro,True.intro⟩,⟨sg30773,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_553All : degreeTree43_553.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30742,degreeTree43_551All,degreeTree43_552All⟩

lemma degreeTree43_554All : degreeTree43_554.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30710,degreeTree43_550All,degreeTree43_553All⟩

lemma degreeTree43_555All : degreeTree43_555.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30783,⟨sg30779,⟨sg30777,⟨sg30776,⟨sg30775,True.intro,True.intro⟩,True.intro⟩,⟨sg30778,True.intro,True.intro⟩⟩,⟨sg30781,⟨sg30780,True.intro,True.intro⟩,⟨sg30782,True.intro,True.intro⟩⟩⟩,⟨sg30787,⟨sg30785,⟨sg30784,True.intro,True.intro⟩,⟨sg30786,True.intro,True.intro⟩⟩,⟨sg30789,⟨sg30788,True.intro,True.intro⟩,⟨sg30790,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_556All : degreeTree43_556.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30799,⟨sg30795,⟨sg30793,⟨sg30792,True.intro,True.intro⟩,⟨sg30794,True.intro,True.intro⟩⟩,⟨sg30797,⟨sg30796,True.intro,True.intro⟩,⟨sg30798,True.intro,True.intro⟩⟩⟩,⟨sg30803,⟨sg30801,⟨sg30800,True.intro,True.intro⟩,⟨sg30802,True.intro,True.intro⟩⟩,⟨sg30805,⟨sg30804,True.intro,True.intro⟩,⟨sg30806,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_557All : degreeTree43_557.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30791,degreeTree43_555All,degreeTree43_556All⟩

lemma degreeTree43_558All : degreeTree43_558.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30823,⟨sg30815,⟨sg30811,⟨sg30809,⟨sg30808,True.intro,True.intro⟩,⟨sg30810,True.intro,True.intro⟩⟩,⟨sg30813,⟨sg30812,True.intro,True.intro⟩,⟨sg30814,True.intro,True.intro⟩⟩⟩,⟨sg30819,⟨sg30817,⟨sg30816,True.intro,True.intro⟩,⟨sg30818,True.intro,True.intro⟩⟩,⟨sg30821,⟨sg30820,True.intro,True.intro⟩,⟨sg30822,True.intro,True.intro⟩⟩⟩⟩,⟨sg30831,⟨sg30827,⟨sg30825,⟨sg30824,True.intro,True.intro⟩,⟨sg30826,True.intro,True.intro⟩⟩,⟨sg30829,⟨sg30828,True.intro,True.intro⟩,⟨sg30830,True.intro,True.intro⟩⟩⟩,⟨sg30835,⟨sg30833,⟨sg30832,True.intro,True.intro⟩,⟨sg30834,True.intro,True.intro⟩⟩,⟨sg30837,⟨sg30836,True.intro,True.intro⟩,⟨sg30838,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_559All : degreeTree43_559.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30807,degreeTree43_557All,degreeTree43_558All⟩

lemma degreeTree43_560All : degreeTree43_560.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30855,⟨sg30847,⟨sg30843,⟨sg30841,⟨sg30840,True.intro,True.intro⟩,⟨sg30842,True.intro,True.intro⟩⟩,⟨sg30845,⟨sg30844,True.intro,True.intro⟩,⟨sg30846,True.intro,True.intro⟩⟩⟩,⟨sg30851,⟨sg30849,⟨sg30848,True.intro,True.intro⟩,⟨sg30850,True.intro,True.intro⟩⟩,⟨sg30853,⟨sg30852,True.intro,True.intro⟩,⟨sg30854,True.intro,True.intro⟩⟩⟩⟩,⟨sg30863,⟨sg30859,⟨sg30857,⟨sg30856,True.intro,True.intro⟩,⟨sg30858,True.intro,True.intro⟩⟩,⟨sg30861,⟨sg30860,True.intro,True.intro⟩,⟨sg30862,True.intro,True.intro⟩⟩⟩,⟨sg30867,⟨sg30865,⟨sg30864,True.intro,True.intro⟩,⟨sg30866,True.intro,True.intro⟩⟩,⟨sg30869,⟨sg30868,True.intro,True.intro⟩,⟨sg30870,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_561All : degreeTree43_561.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30887,⟨sg30879,⟨sg30875,⟨sg30873,⟨sg30872,True.intro,True.intro⟩,⟨sg30874,True.intro,True.intro⟩⟩,⟨sg30877,⟨sg30876,True.intro,True.intro⟩,⟨sg30878,True.intro,True.intro⟩⟩⟩,⟨sg30883,⟨sg30881,⟨sg30880,True.intro,True.intro⟩,⟨sg30882,True.intro,True.intro⟩⟩,⟨sg30885,⟨sg30884,True.intro,True.intro⟩,⟨sg30886,True.intro,True.intro⟩⟩⟩⟩,⟨sg30895,⟨sg30891,⟨sg30889,⟨sg30888,True.intro,True.intro⟩,⟨sg30890,True.intro,True.intro⟩⟩,⟨sg30893,⟨sg30892,True.intro,True.intro⟩,⟨sg30894,True.intro,True.intro⟩⟩⟩,⟨sg30899,⟨sg30897,⟨sg30896,True.intro,True.intro⟩,⟨sg30898,True.intro,True.intro⟩⟩,⟨sg30901,⟨sg30900,True.intro,True.intro⟩,⟨sg30902,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_562All : degreeTree43_562.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30871,degreeTree43_560All,degreeTree43_561All⟩

lemma degreeTree43_563All : degreeTree43_563.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30839,degreeTree43_559All,degreeTree43_562All⟩

lemma degreeTree43_564All : degreeTree43_564.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30774,degreeTree43_554All,degreeTree43_563All⟩

lemma degreeTree43_565All : degreeTree43_565.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30645,degreeTree43_545All,degreeTree43_564All⟩

lemma degreeTree43_566All : degreeTree43_566.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30387,degreeTree43_526All,degreeTree43_565All⟩

lemma degreeTree43_567All : degreeTree43_567.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30912,⟨sg30908,⟨sg30906,⟨sg30905,⟨sg30904,True.intro,True.intro⟩,True.intro⟩,⟨sg30907,True.intro,True.intro⟩⟩,⟨sg30910,⟨sg30909,True.intro,True.intro⟩,⟨sg30911,True.intro,True.intro⟩⟩⟩,⟨sg30916,⟨sg30914,⟨sg30913,True.intro,True.intro⟩,⟨sg30915,True.intro,True.intro⟩⟩,⟨sg30918,⟨sg30917,True.intro,True.intro⟩,⟨sg30919,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_568All : degreeTree43_568.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30928,⟨sg30924,⟨sg30922,⟨sg30921,True.intro,True.intro⟩,⟨sg30923,True.intro,True.intro⟩⟩,⟨sg30926,⟨sg30925,True.intro,True.intro⟩,⟨sg30927,True.intro,True.intro⟩⟩⟩,⟨sg30932,⟨sg30930,⟨sg30929,True.intro,True.intro⟩,⟨sg30931,True.intro,True.intro⟩⟩,⟨sg30934,⟨sg30933,True.intro,True.intro⟩,⟨sg30935,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_569All : degreeTree43_569.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30920,degreeTree43_567All,degreeTree43_568All⟩

lemma degreeTree43_570All : degreeTree43_570.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30952,⟨sg30944,⟨sg30940,⟨sg30938,⟨sg30937,True.intro,True.intro⟩,⟨sg30939,True.intro,True.intro⟩⟩,⟨sg30942,⟨sg30941,True.intro,True.intro⟩,⟨sg30943,True.intro,True.intro⟩⟩⟩,⟨sg30948,⟨sg30946,⟨sg30945,True.intro,True.intro⟩,⟨sg30947,True.intro,True.intro⟩⟩,⟨sg30950,⟨sg30949,True.intro,True.intro⟩,⟨sg30951,True.intro,True.intro⟩⟩⟩⟩,⟨sg30960,⟨sg30956,⟨sg30954,⟨sg30953,True.intro,True.intro⟩,⟨sg30955,True.intro,True.intro⟩⟩,⟨sg30958,⟨sg30957,True.intro,True.intro⟩,⟨sg30959,True.intro,True.intro⟩⟩⟩,⟨sg30964,⟨sg30962,⟨sg30961,True.intro,True.intro⟩,⟨sg30963,True.intro,True.intro⟩⟩,⟨sg30966,⟨sg30965,True.intro,True.intro⟩,⟨sg30967,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_571All : degreeTree43_571.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30936,degreeTree43_569All,degreeTree43_570All⟩

lemma degreeTree43_572All : degreeTree43_572.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30984,⟨sg30976,⟨sg30972,⟨sg30970,⟨sg30969,True.intro,True.intro⟩,⟨sg30971,True.intro,True.intro⟩⟩,⟨sg30974,⟨sg30973,True.intro,True.intro⟩,⟨sg30975,True.intro,True.intro⟩⟩⟩,⟨sg30980,⟨sg30978,⟨sg30977,True.intro,True.intro⟩,⟨sg30979,True.intro,True.intro⟩⟩,⟨sg30982,⟨sg30981,True.intro,True.intro⟩,⟨sg30983,True.intro,True.intro⟩⟩⟩⟩,⟨sg30992,⟨sg30988,⟨sg30986,⟨sg30985,True.intro,True.intro⟩,⟨sg30987,True.intro,True.intro⟩⟩,⟨sg30990,⟨sg30989,True.intro,True.intro⟩,⟨sg30991,True.intro,True.intro⟩⟩⟩,⟨sg30996,⟨sg30994,⟨sg30993,True.intro,True.intro⟩,⟨sg30995,True.intro,True.intro⟩⟩,⟨sg30998,⟨sg30997,True.intro,True.intro⟩,⟨sg30999,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_573All : degreeTree43_573.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31016,⟨sg31008,⟨sg31004,⟨sg31002,⟨sg31001,True.intro,True.intro⟩,⟨sg31003,True.intro,True.intro⟩⟩,⟨sg31006,⟨sg31005,True.intro,True.intro⟩,⟨sg31007,True.intro,True.intro⟩⟩⟩,⟨sg31012,⟨sg31010,⟨sg31009,True.intro,True.intro⟩,⟨sg31011,True.intro,True.intro⟩⟩,⟨sg31014,⟨sg31013,True.intro,True.intro⟩,⟨sg31015,True.intro,True.intro⟩⟩⟩⟩,⟨sg31024,⟨sg31020,⟨sg31018,⟨sg31017,True.intro,True.intro⟩,⟨sg31019,True.intro,True.intro⟩⟩,⟨sg31022,⟨sg31021,True.intro,True.intro⟩,⟨sg31023,True.intro,True.intro⟩⟩⟩,⟨sg31028,⟨sg31026,⟨sg31025,True.intro,True.intro⟩,⟨sg31027,True.intro,True.intro⟩⟩,⟨sg31030,⟨sg31029,True.intro,True.intro⟩,⟨sg31031,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_574All : degreeTree43_574.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31000,degreeTree43_572All,degreeTree43_573All⟩

lemma degreeTree43_575All : degreeTree43_575.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30968,degreeTree43_571All,degreeTree43_574All⟩

lemma degreeTree43_576All : degreeTree43_576.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31041,⟨sg31037,⟨sg31035,⟨sg31034,⟨sg31033,True.intro,True.intro⟩,True.intro⟩,⟨sg31036,True.intro,True.intro⟩⟩,⟨sg31039,⟨sg31038,True.intro,True.intro⟩,⟨sg31040,True.intro,True.intro⟩⟩⟩,⟨sg31045,⟨sg31043,⟨sg31042,True.intro,True.intro⟩,⟨sg31044,True.intro,True.intro⟩⟩,⟨sg31047,⟨sg31046,True.intro,True.intro⟩,⟨sg31048,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_577All : degreeTree43_577.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31057,⟨sg31053,⟨sg31051,⟨sg31050,True.intro,True.intro⟩,⟨sg31052,True.intro,True.intro⟩⟩,⟨sg31055,⟨sg31054,True.intro,True.intro⟩,⟨sg31056,True.intro,True.intro⟩⟩⟩,⟨sg31061,⟨sg31059,⟨sg31058,True.intro,True.intro⟩,⟨sg31060,True.intro,True.intro⟩⟩,⟨sg31063,⟨sg31062,True.intro,True.intro⟩,⟨sg31064,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_578All : degreeTree43_578.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31049,degreeTree43_576All,degreeTree43_577All⟩

lemma degreeTree43_579All : degreeTree43_579.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31081,⟨sg31073,⟨sg31069,⟨sg31067,⟨sg31066,True.intro,True.intro⟩,⟨sg31068,True.intro,True.intro⟩⟩,⟨sg31071,⟨sg31070,True.intro,True.intro⟩,⟨sg31072,True.intro,True.intro⟩⟩⟩,⟨sg31077,⟨sg31075,⟨sg31074,True.intro,True.intro⟩,⟨sg31076,True.intro,True.intro⟩⟩,⟨sg31079,⟨sg31078,True.intro,True.intro⟩,⟨sg31080,True.intro,True.intro⟩⟩⟩⟩,⟨sg31089,⟨sg31085,⟨sg31083,⟨sg31082,True.intro,True.intro⟩,⟨sg31084,True.intro,True.intro⟩⟩,⟨sg31087,⟨sg31086,True.intro,True.intro⟩,⟨sg31088,True.intro,True.intro⟩⟩⟩,⟨sg31093,⟨sg31091,⟨sg31090,True.intro,True.intro⟩,⟨sg31092,True.intro,True.intro⟩⟩,⟨sg31095,⟨sg31094,True.intro,True.intro⟩,⟨sg31096,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_580All : degreeTree43_580.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31065,degreeTree43_578All,degreeTree43_579All⟩

lemma degreeTree43_581All : degreeTree43_581.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31113,⟨sg31105,⟨sg31101,⟨sg31099,⟨sg31098,True.intro,True.intro⟩,⟨sg31100,True.intro,True.intro⟩⟩,⟨sg31103,⟨sg31102,True.intro,True.intro⟩,⟨sg31104,True.intro,True.intro⟩⟩⟩,⟨sg31109,⟨sg31107,⟨sg31106,True.intro,True.intro⟩,⟨sg31108,True.intro,True.intro⟩⟩,⟨sg31111,⟨sg31110,True.intro,True.intro⟩,⟨sg31112,True.intro,True.intro⟩⟩⟩⟩,⟨sg31121,⟨sg31117,⟨sg31115,⟨sg31114,True.intro,True.intro⟩,⟨sg31116,True.intro,True.intro⟩⟩,⟨sg31119,⟨sg31118,True.intro,True.intro⟩,⟨sg31120,True.intro,True.intro⟩⟩⟩,⟨sg31125,⟨sg31123,⟨sg31122,True.intro,True.intro⟩,⟨sg31124,True.intro,True.intro⟩⟩,⟨sg31127,⟨sg31126,True.intro,True.intro⟩,⟨sg31128,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_582All : degreeTree43_582.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31145,⟨sg31137,⟨sg31133,⟨sg31131,⟨sg31130,True.intro,True.intro⟩,⟨sg31132,True.intro,True.intro⟩⟩,⟨sg31135,⟨sg31134,True.intro,True.intro⟩,⟨sg31136,True.intro,True.intro⟩⟩⟩,⟨sg31141,⟨sg31139,⟨sg31138,True.intro,True.intro⟩,⟨sg31140,True.intro,True.intro⟩⟩,⟨sg31143,⟨sg31142,True.intro,True.intro⟩,⟨sg31144,True.intro,True.intro⟩⟩⟩⟩,⟨sg31153,⟨sg31149,⟨sg31147,⟨sg31146,True.intro,True.intro⟩,⟨sg31148,True.intro,True.intro⟩⟩,⟨sg31151,⟨sg31150,True.intro,True.intro⟩,⟨sg31152,True.intro,True.intro⟩⟩⟩,⟨sg31157,⟨sg31155,⟨sg31154,True.intro,True.intro⟩,⟨sg31156,True.intro,True.intro⟩⟩,⟨sg31159,⟨sg31158,True.intro,True.intro⟩,⟨sg31160,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_583All : degreeTree43_583.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31129,degreeTree43_581All,degreeTree43_582All⟩

lemma degreeTree43_584All : degreeTree43_584.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31097,degreeTree43_580All,degreeTree43_583All⟩

lemma degreeTree43_585All : degreeTree43_585.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31032,degreeTree43_575All,degreeTree43_584All⟩

lemma degreeTree43_586All : degreeTree43_586.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31170,⟨sg31166,⟨sg31164,⟨sg31163,⟨sg31162,True.intro,True.intro⟩,True.intro⟩,⟨sg31165,True.intro,True.intro⟩⟩,⟨sg31168,⟨sg31167,True.intro,True.intro⟩,⟨sg31169,True.intro,True.intro⟩⟩⟩,⟨sg31174,⟨sg31172,⟨sg31171,True.intro,True.intro⟩,⟨sg31173,True.intro,True.intro⟩⟩,⟨sg31176,⟨sg31175,True.intro,True.intro⟩,⟨sg31177,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_587All : degreeTree43_587.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31186,⟨sg31182,⟨sg31180,⟨sg31179,True.intro,True.intro⟩,⟨sg31181,True.intro,True.intro⟩⟩,⟨sg31184,⟨sg31183,True.intro,True.intro⟩,⟨sg31185,True.intro,True.intro⟩⟩⟩,⟨sg31190,⟨sg31188,⟨sg31187,True.intro,True.intro⟩,⟨sg31189,True.intro,True.intro⟩⟩,⟨sg31192,⟨sg31191,True.intro,True.intro⟩,⟨sg31193,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_588All : degreeTree43_588.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31178,degreeTree43_586All,degreeTree43_587All⟩

lemma degreeTree43_589All : degreeTree43_589.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31210,⟨sg31202,⟨sg31198,⟨sg31196,⟨sg31195,True.intro,True.intro⟩,⟨sg31197,True.intro,True.intro⟩⟩,⟨sg31200,⟨sg31199,True.intro,True.intro⟩,⟨sg31201,True.intro,True.intro⟩⟩⟩,⟨sg31206,⟨sg31204,⟨sg31203,True.intro,True.intro⟩,⟨sg31205,True.intro,True.intro⟩⟩,⟨sg31208,⟨sg31207,True.intro,True.intro⟩,⟨sg31209,True.intro,True.intro⟩⟩⟩⟩,⟨sg31218,⟨sg31214,⟨sg31212,⟨sg31211,True.intro,True.intro⟩,⟨sg31213,True.intro,True.intro⟩⟩,⟨sg31216,⟨sg31215,True.intro,True.intro⟩,⟨sg31217,True.intro,True.intro⟩⟩⟩,⟨sg31222,⟨sg31220,⟨sg31219,True.intro,True.intro⟩,⟨sg31221,True.intro,True.intro⟩⟩,⟨sg31224,⟨sg31223,True.intro,True.intro⟩,⟨sg31225,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_590All : degreeTree43_590.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31194,degreeTree43_588All,degreeTree43_589All⟩

lemma degreeTree43_591All : degreeTree43_591.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31242,⟨sg31234,⟨sg31230,⟨sg31228,⟨sg31227,True.intro,True.intro⟩,⟨sg31229,True.intro,True.intro⟩⟩,⟨sg31232,⟨sg31231,True.intro,True.intro⟩,⟨sg31233,True.intro,True.intro⟩⟩⟩,⟨sg31238,⟨sg31236,⟨sg31235,True.intro,True.intro⟩,⟨sg31237,True.intro,True.intro⟩⟩,⟨sg31240,⟨sg31239,True.intro,True.intro⟩,⟨sg31241,True.intro,True.intro⟩⟩⟩⟩,⟨sg31250,⟨sg31246,⟨sg31244,⟨sg31243,True.intro,True.intro⟩,⟨sg31245,True.intro,True.intro⟩⟩,⟨sg31248,⟨sg31247,True.intro,True.intro⟩,⟨sg31249,True.intro,True.intro⟩⟩⟩,⟨sg31254,⟨sg31252,⟨sg31251,True.intro,True.intro⟩,⟨sg31253,True.intro,True.intro⟩⟩,⟨sg31256,⟨sg31255,True.intro,True.intro⟩,⟨sg31257,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_592All : degreeTree43_592.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31274,⟨sg31266,⟨sg31262,⟨sg31260,⟨sg31259,True.intro,True.intro⟩,⟨sg31261,True.intro,True.intro⟩⟩,⟨sg31264,⟨sg31263,True.intro,True.intro⟩,⟨sg31265,True.intro,True.intro⟩⟩⟩,⟨sg31270,⟨sg31268,⟨sg31267,True.intro,True.intro⟩,⟨sg31269,True.intro,True.intro⟩⟩,⟨sg31272,⟨sg31271,True.intro,True.intro⟩,⟨sg31273,True.intro,True.intro⟩⟩⟩⟩,⟨sg31282,⟨sg31278,⟨sg31276,⟨sg31275,True.intro,True.intro⟩,⟨sg31277,True.intro,True.intro⟩⟩,⟨sg31280,⟨sg31279,True.intro,True.intro⟩,⟨sg31281,True.intro,True.intro⟩⟩⟩,⟨sg31286,⟨sg31284,⟨sg31283,True.intro,True.intro⟩,⟨sg31285,True.intro,True.intro⟩⟩,⟨sg31288,⟨sg31287,True.intro,True.intro⟩,⟨sg31289,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_593All : degreeTree43_593.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31258,degreeTree43_591All,degreeTree43_592All⟩

lemma degreeTree43_594All : degreeTree43_594.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31226,degreeTree43_590All,degreeTree43_593All⟩

lemma degreeTree43_595All : degreeTree43_595.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31299,⟨sg31295,⟨sg31293,⟨sg31292,⟨sg31291,True.intro,True.intro⟩,True.intro⟩,⟨sg31294,True.intro,True.intro⟩⟩,⟨sg31297,⟨sg31296,True.intro,True.intro⟩,⟨sg31298,True.intro,True.intro⟩⟩⟩,⟨sg31303,⟨sg31301,⟨sg31300,True.intro,True.intro⟩,⟨sg31302,True.intro,True.intro⟩⟩,⟨sg31305,⟨sg31304,True.intro,True.intro⟩,⟨sg31306,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_596All : degreeTree43_596.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31315,⟨sg31311,⟨sg31309,⟨sg31308,True.intro,True.intro⟩,⟨sg31310,True.intro,True.intro⟩⟩,⟨sg31313,⟨sg31312,True.intro,True.intro⟩,⟨sg31314,True.intro,True.intro⟩⟩⟩,⟨sg31319,⟨sg31317,⟨sg31316,True.intro,True.intro⟩,⟨sg31318,True.intro,True.intro⟩⟩,⟨sg31321,⟨sg31320,True.intro,True.intro⟩,⟨sg31322,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_597All : degreeTree43_597.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31307,degreeTree43_595All,degreeTree43_596All⟩

lemma degreeTree43_598All : degreeTree43_598.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31339,⟨sg31331,⟨sg31327,⟨sg31325,⟨sg31324,True.intro,True.intro⟩,⟨sg31326,True.intro,True.intro⟩⟩,⟨sg31329,⟨sg31328,True.intro,True.intro⟩,⟨sg31330,True.intro,True.intro⟩⟩⟩,⟨sg31335,⟨sg31333,⟨sg31332,True.intro,True.intro⟩,⟨sg31334,True.intro,True.intro⟩⟩,⟨sg31337,⟨sg31336,True.intro,True.intro⟩,⟨sg31338,True.intro,True.intro⟩⟩⟩⟩,⟨sg31347,⟨sg31343,⟨sg31341,⟨sg31340,True.intro,True.intro⟩,⟨sg31342,True.intro,True.intro⟩⟩,⟨sg31345,⟨sg31344,True.intro,True.intro⟩,⟨sg31346,True.intro,True.intro⟩⟩⟩,⟨sg31351,⟨sg31349,⟨sg31348,True.intro,True.intro⟩,⟨sg31350,True.intro,True.intro⟩⟩,⟨sg31353,⟨sg31352,True.intro,True.intro⟩,⟨sg31354,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_599All : degreeTree43_599.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31323,degreeTree43_597All,degreeTree43_598All⟩

lemma degreeTree43_600All : degreeTree43_600.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31371,⟨sg31363,⟨sg31359,⟨sg31357,⟨sg31356,True.intro,True.intro⟩,⟨sg31358,True.intro,True.intro⟩⟩,⟨sg31361,⟨sg31360,True.intro,True.intro⟩,⟨sg31362,True.intro,True.intro⟩⟩⟩,⟨sg31367,⟨sg31365,⟨sg31364,True.intro,True.intro⟩,⟨sg31366,True.intro,True.intro⟩⟩,⟨sg31369,⟨sg31368,True.intro,True.intro⟩,⟨sg31370,True.intro,True.intro⟩⟩⟩⟩,⟨sg31379,⟨sg31375,⟨sg31373,⟨sg31372,True.intro,True.intro⟩,⟨sg31374,True.intro,True.intro⟩⟩,⟨sg31377,⟨sg31376,True.intro,True.intro⟩,⟨sg31378,True.intro,True.intro⟩⟩⟩,⟨sg31383,⟨sg31381,⟨sg31380,True.intro,True.intro⟩,⟨sg31382,True.intro,True.intro⟩⟩,⟨sg31385,⟨sg31384,True.intro,True.intro⟩,⟨sg31386,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_601All : degreeTree43_601.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31403,⟨sg31395,⟨sg31391,⟨sg31389,⟨sg31388,True.intro,True.intro⟩,⟨sg31390,True.intro,True.intro⟩⟩,⟨sg31393,⟨sg31392,True.intro,True.intro⟩,⟨sg31394,True.intro,True.intro⟩⟩⟩,⟨sg31399,⟨sg31397,⟨sg31396,True.intro,True.intro⟩,⟨sg31398,True.intro,True.intro⟩⟩,⟨sg31401,⟨sg31400,True.intro,True.intro⟩,⟨sg31402,True.intro,True.intro⟩⟩⟩⟩,⟨sg31411,⟨sg31407,⟨sg31405,⟨sg31404,True.intro,True.intro⟩,⟨sg31406,True.intro,True.intro⟩⟩,⟨sg31409,⟨sg31408,True.intro,True.intro⟩,⟨sg31410,True.intro,True.intro⟩⟩⟩,⟨sg31415,⟨sg31413,⟨sg31412,True.intro,True.intro⟩,⟨sg31414,True.intro,True.intro⟩⟩,⟨sg31417,⟨sg31416,True.intro,True.intro⟩,⟨sg31418,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_602All : degreeTree43_602.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31387,degreeTree43_600All,degreeTree43_601All⟩

lemma degreeTree43_603All : degreeTree43_603.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31355,degreeTree43_599All,degreeTree43_602All⟩

lemma degreeTree43_604All : degreeTree43_604.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31290,degreeTree43_594All,degreeTree43_603All⟩

lemma degreeTree43_605All : degreeTree43_605.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31161,degreeTree43_585All,degreeTree43_604All⟩

lemma degreeTree43_606All : degreeTree43_606.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31428,⟨sg31424,⟨sg31422,⟨sg31421,⟨sg31420,True.intro,True.intro⟩,True.intro⟩,⟨sg31423,True.intro,True.intro⟩⟩,⟨sg31426,⟨sg31425,True.intro,True.intro⟩,⟨sg31427,True.intro,True.intro⟩⟩⟩,⟨sg31432,⟨sg31430,⟨sg31429,True.intro,True.intro⟩,⟨sg31431,True.intro,True.intro⟩⟩,⟨sg31434,⟨sg31433,True.intro,True.intro⟩,⟨sg31435,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_607All : degreeTree43_607.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31444,⟨sg31440,⟨sg31438,⟨sg31437,True.intro,True.intro⟩,⟨sg31439,True.intro,True.intro⟩⟩,⟨sg31442,⟨sg31441,True.intro,True.intro⟩,⟨sg31443,True.intro,True.intro⟩⟩⟩,⟨sg31448,⟨sg31446,⟨sg31445,True.intro,True.intro⟩,⟨sg31447,True.intro,True.intro⟩⟩,⟨sg31450,⟨sg31449,True.intro,True.intro⟩,⟨sg31451,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_608All : degreeTree43_608.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31436,degreeTree43_606All,degreeTree43_607All⟩

lemma degreeTree43_609All : degreeTree43_609.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31468,⟨sg31460,⟨sg31456,⟨sg31454,⟨sg31453,True.intro,True.intro⟩,⟨sg31455,True.intro,True.intro⟩⟩,⟨sg31458,⟨sg31457,True.intro,True.intro⟩,⟨sg31459,True.intro,True.intro⟩⟩⟩,⟨sg31464,⟨sg31462,⟨sg31461,True.intro,True.intro⟩,⟨sg31463,True.intro,True.intro⟩⟩,⟨sg31466,⟨sg31465,True.intro,True.intro⟩,⟨sg31467,True.intro,True.intro⟩⟩⟩⟩,⟨sg31476,⟨sg31472,⟨sg31470,⟨sg31469,True.intro,True.intro⟩,⟨sg31471,True.intro,True.intro⟩⟩,⟨sg31474,⟨sg31473,True.intro,True.intro⟩,⟨sg31475,True.intro,True.intro⟩⟩⟩,⟨sg31480,⟨sg31478,⟨sg31477,True.intro,True.intro⟩,⟨sg31479,True.intro,True.intro⟩⟩,⟨sg31482,⟨sg31481,True.intro,True.intro⟩,⟨sg31483,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_610All : degreeTree43_610.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31452,degreeTree43_608All,degreeTree43_609All⟩

lemma degreeTree43_611All : degreeTree43_611.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31500,⟨sg31492,⟨sg31488,⟨sg31486,⟨sg31485,True.intro,True.intro⟩,⟨sg31487,True.intro,True.intro⟩⟩,⟨sg31490,⟨sg31489,True.intro,True.intro⟩,⟨sg31491,True.intro,True.intro⟩⟩⟩,⟨sg31496,⟨sg31494,⟨sg31493,True.intro,True.intro⟩,⟨sg31495,True.intro,True.intro⟩⟩,⟨sg31498,⟨sg31497,True.intro,True.intro⟩,⟨sg31499,True.intro,True.intro⟩⟩⟩⟩,⟨sg31508,⟨sg31504,⟨sg31502,⟨sg31501,True.intro,True.intro⟩,⟨sg31503,True.intro,True.intro⟩⟩,⟨sg31506,⟨sg31505,True.intro,True.intro⟩,⟨sg31507,True.intro,True.intro⟩⟩⟩,⟨sg31512,⟨sg31510,⟨sg31509,True.intro,True.intro⟩,⟨sg31511,True.intro,True.intro⟩⟩,⟨sg31514,⟨sg31513,True.intro,True.intro⟩,⟨sg31515,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_612All : degreeTree43_612.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31532,⟨sg31524,⟨sg31520,⟨sg31518,⟨sg31517,True.intro,True.intro⟩,⟨sg31519,True.intro,True.intro⟩⟩,⟨sg31522,⟨sg31521,True.intro,True.intro⟩,⟨sg31523,True.intro,True.intro⟩⟩⟩,⟨sg31528,⟨sg31526,⟨sg31525,True.intro,True.intro⟩,⟨sg31527,True.intro,True.intro⟩⟩,⟨sg31530,⟨sg31529,True.intro,True.intro⟩,⟨sg31531,True.intro,True.intro⟩⟩⟩⟩,⟨sg31540,⟨sg31536,⟨sg31534,⟨sg31533,True.intro,True.intro⟩,⟨sg31535,True.intro,True.intro⟩⟩,⟨sg31538,⟨sg31537,True.intro,True.intro⟩,⟨sg31539,True.intro,True.intro⟩⟩⟩,⟨sg31544,⟨sg31542,⟨sg31541,True.intro,True.intro⟩,⟨sg31543,True.intro,True.intro⟩⟩,⟨sg31546,⟨sg31545,True.intro,True.intro⟩,⟨sg31547,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_613All : degreeTree43_613.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31516,degreeTree43_611All,degreeTree43_612All⟩

lemma degreeTree43_614All : degreeTree43_614.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31484,degreeTree43_610All,degreeTree43_613All⟩

lemma degreeTree43_615All : degreeTree43_615.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31557,⟨sg31553,⟨sg31551,⟨sg31550,⟨sg31549,True.intro,True.intro⟩,True.intro⟩,⟨sg31552,True.intro,True.intro⟩⟩,⟨sg31555,⟨sg31554,True.intro,True.intro⟩,⟨sg31556,True.intro,True.intro⟩⟩⟩,⟨sg31561,⟨sg31559,⟨sg31558,True.intro,True.intro⟩,⟨sg31560,True.intro,True.intro⟩⟩,⟨sg31563,⟨sg31562,True.intro,True.intro⟩,⟨sg31564,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_616All : degreeTree43_616.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31573,⟨sg31569,⟨sg31567,⟨sg31566,True.intro,True.intro⟩,⟨sg31568,True.intro,True.intro⟩⟩,⟨sg31571,⟨sg31570,True.intro,True.intro⟩,⟨sg31572,True.intro,True.intro⟩⟩⟩,⟨sg31577,⟨sg31575,⟨sg31574,True.intro,True.intro⟩,⟨sg31576,True.intro,True.intro⟩⟩,⟨sg31579,⟨sg31578,True.intro,True.intro⟩,⟨sg31580,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_617All : degreeTree43_617.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31565,degreeTree43_615All,degreeTree43_616All⟩

lemma degreeTree43_618All : degreeTree43_618.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31597,⟨sg31589,⟨sg31585,⟨sg31583,⟨sg31582,True.intro,True.intro⟩,⟨sg31584,True.intro,True.intro⟩⟩,⟨sg31587,⟨sg31586,True.intro,True.intro⟩,⟨sg31588,True.intro,True.intro⟩⟩⟩,⟨sg31593,⟨sg31591,⟨sg31590,True.intro,True.intro⟩,⟨sg31592,True.intro,True.intro⟩⟩,⟨sg31595,⟨sg31594,True.intro,True.intro⟩,⟨sg31596,True.intro,True.intro⟩⟩⟩⟩,⟨sg31605,⟨sg31601,⟨sg31599,⟨sg31598,True.intro,True.intro⟩,⟨sg31600,True.intro,True.intro⟩⟩,⟨sg31603,⟨sg31602,True.intro,True.intro⟩,⟨sg31604,True.intro,True.intro⟩⟩⟩,⟨sg31609,⟨sg31607,⟨sg31606,True.intro,True.intro⟩,⟨sg31608,True.intro,True.intro⟩⟩,⟨sg31611,⟨sg31610,True.intro,True.intro⟩,⟨sg31612,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_619All : degreeTree43_619.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31581,degreeTree43_617All,degreeTree43_618All⟩

lemma degreeTree43_620All : degreeTree43_620.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31629,⟨sg31621,⟨sg31617,⟨sg31615,⟨sg31614,True.intro,True.intro⟩,⟨sg31616,True.intro,True.intro⟩⟩,⟨sg31619,⟨sg31618,True.intro,True.intro⟩,⟨sg31620,True.intro,True.intro⟩⟩⟩,⟨sg31625,⟨sg31623,⟨sg31622,True.intro,True.intro⟩,⟨sg31624,True.intro,True.intro⟩⟩,⟨sg31627,⟨sg31626,True.intro,True.intro⟩,⟨sg31628,True.intro,True.intro⟩⟩⟩⟩,⟨sg31637,⟨sg31633,⟨sg31631,⟨sg31630,True.intro,True.intro⟩,⟨sg31632,True.intro,True.intro⟩⟩,⟨sg31635,⟨sg31634,True.intro,True.intro⟩,⟨sg31636,True.intro,True.intro⟩⟩⟩,⟨sg31641,⟨sg31639,⟨sg31638,True.intro,True.intro⟩,⟨sg31640,True.intro,True.intro⟩⟩,⟨sg31643,⟨sg31642,True.intro,True.intro⟩,⟨sg31644,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_621All : degreeTree43_621.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31661,⟨sg31653,⟨sg31649,⟨sg31647,⟨sg31646,True.intro,True.intro⟩,⟨sg31648,True.intro,True.intro⟩⟩,⟨sg31651,⟨sg31650,True.intro,True.intro⟩,⟨sg31652,True.intro,True.intro⟩⟩⟩,⟨sg31657,⟨sg31655,⟨sg31654,True.intro,True.intro⟩,⟨sg31656,True.intro,True.intro⟩⟩,⟨sg31659,⟨sg31658,True.intro,True.intro⟩,⟨sg31660,True.intro,True.intro⟩⟩⟩⟩,⟨sg31669,⟨sg31665,⟨sg31663,⟨sg31662,True.intro,True.intro⟩,⟨sg31664,True.intro,True.intro⟩⟩,⟨sg31667,⟨sg31666,True.intro,True.intro⟩,⟨sg31668,True.intro,True.intro⟩⟩⟩,⟨sg31673,⟨sg31671,⟨sg31670,True.intro,True.intro⟩,⟨sg31672,True.intro,True.intro⟩⟩,⟨sg31675,⟨sg31674,True.intro,True.intro⟩,⟨sg31676,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_622All : degreeTree43_622.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31645,degreeTree43_620All,degreeTree43_621All⟩

lemma degreeTree43_623All : degreeTree43_623.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31613,degreeTree43_619All,degreeTree43_622All⟩

lemma degreeTree43_624All : degreeTree43_624.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31548,degreeTree43_614All,degreeTree43_623All⟩

lemma degreeTree43_625All : degreeTree43_625.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31686,⟨sg31682,⟨sg31680,⟨sg31679,⟨sg31678,True.intro,True.intro⟩,True.intro⟩,⟨sg31681,True.intro,True.intro⟩⟩,⟨sg31684,⟨sg31683,True.intro,True.intro⟩,⟨sg31685,True.intro,True.intro⟩⟩⟩,⟨sg31690,⟨sg31688,⟨sg31687,True.intro,True.intro⟩,⟨sg31689,True.intro,True.intro⟩⟩,⟨sg31692,⟨sg31691,True.intro,True.intro⟩,⟨sg31693,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_626All : degreeTree43_626.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31702,⟨sg31698,⟨sg31696,⟨sg31695,True.intro,True.intro⟩,⟨sg31697,True.intro,True.intro⟩⟩,⟨sg31700,⟨sg31699,True.intro,True.intro⟩,⟨sg31701,True.intro,True.intro⟩⟩⟩,⟨sg31706,⟨sg31704,⟨sg31703,True.intro,True.intro⟩,⟨sg31705,True.intro,True.intro⟩⟩,⟨sg31708,⟨sg31707,True.intro,True.intro⟩,⟨sg31709,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_627All : degreeTree43_627.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31694,degreeTree43_625All,degreeTree43_626All⟩

lemma degreeTree43_628All : degreeTree43_628.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31726,⟨sg31718,⟨sg31714,⟨sg31712,⟨sg31711,True.intro,True.intro⟩,⟨sg31713,True.intro,True.intro⟩⟩,⟨sg31716,⟨sg31715,True.intro,True.intro⟩,⟨sg31717,True.intro,True.intro⟩⟩⟩,⟨sg31722,⟨sg31720,⟨sg31719,True.intro,True.intro⟩,⟨sg31721,True.intro,True.intro⟩⟩,⟨sg31724,⟨sg31723,True.intro,True.intro⟩,⟨sg31725,True.intro,True.intro⟩⟩⟩⟩,⟨sg31734,⟨sg31730,⟨sg31728,⟨sg31727,True.intro,True.intro⟩,⟨sg31729,True.intro,True.intro⟩⟩,⟨sg31732,⟨sg31731,True.intro,True.intro⟩,⟨sg31733,True.intro,True.intro⟩⟩⟩,⟨sg31738,⟨sg31736,⟨sg31735,True.intro,True.intro⟩,⟨sg31737,True.intro,True.intro⟩⟩,⟨sg31740,⟨sg31739,True.intro,True.intro⟩,⟨sg31741,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_629All : degreeTree43_629.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31710,degreeTree43_627All,degreeTree43_628All⟩

lemma degreeTree43_630All : degreeTree43_630.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31758,⟨sg31750,⟨sg31746,⟨sg31744,⟨sg31743,True.intro,True.intro⟩,⟨sg31745,True.intro,True.intro⟩⟩,⟨sg31748,⟨sg31747,True.intro,True.intro⟩,⟨sg31749,True.intro,True.intro⟩⟩⟩,⟨sg31754,⟨sg31752,⟨sg31751,True.intro,True.intro⟩,⟨sg31753,True.intro,True.intro⟩⟩,⟨sg31756,⟨sg31755,True.intro,True.intro⟩,⟨sg31757,True.intro,True.intro⟩⟩⟩⟩,⟨sg31766,⟨sg31762,⟨sg31760,⟨sg31759,True.intro,True.intro⟩,⟨sg31761,True.intro,True.intro⟩⟩,⟨sg31764,⟨sg31763,True.intro,True.intro⟩,⟨sg31765,True.intro,True.intro⟩⟩⟩,⟨sg31770,⟨sg31768,⟨sg31767,True.intro,True.intro⟩,⟨sg31769,True.intro,True.intro⟩⟩,⟨sg31772,⟨sg31771,True.intro,True.intro⟩,⟨sg31773,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_631All : degreeTree43_631.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31790,⟨sg31782,⟨sg31778,⟨sg31776,⟨sg31775,True.intro,True.intro⟩,⟨sg31777,True.intro,True.intro⟩⟩,⟨sg31780,⟨sg31779,True.intro,True.intro⟩,⟨sg31781,True.intro,True.intro⟩⟩⟩,⟨sg31786,⟨sg31784,⟨sg31783,True.intro,True.intro⟩,⟨sg31785,True.intro,True.intro⟩⟩,⟨sg31788,⟨sg31787,True.intro,True.intro⟩,⟨sg31789,True.intro,True.intro⟩⟩⟩⟩,⟨sg31798,⟨sg31794,⟨sg31792,⟨sg31791,True.intro,True.intro⟩,⟨sg31793,True.intro,True.intro⟩⟩,⟨sg31796,⟨sg31795,True.intro,True.intro⟩,⟨sg31797,True.intro,True.intro⟩⟩⟩,⟨sg31802,⟨sg31800,⟨sg31799,True.intro,True.intro⟩,⟨sg31801,True.intro,True.intro⟩⟩,⟨sg31804,⟨sg31803,True.intro,True.intro⟩,⟨sg31805,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_632All : degreeTree43_632.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31774,degreeTree43_630All,degreeTree43_631All⟩

lemma degreeTree43_633All : degreeTree43_633.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31742,degreeTree43_629All,degreeTree43_632All⟩

lemma degreeTree43_634All : degreeTree43_634.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31815,⟨sg31811,⟨sg31809,⟨sg31808,⟨sg31807,True.intro,True.intro⟩,True.intro⟩,⟨sg31810,True.intro,True.intro⟩⟩,⟨sg31813,⟨sg31812,True.intro,True.intro⟩,⟨sg31814,True.intro,True.intro⟩⟩⟩,⟨sg31819,⟨sg31817,⟨sg31816,True.intro,True.intro⟩,⟨sg31818,True.intro,True.intro⟩⟩,⟨sg31821,⟨sg31820,True.intro,True.intro⟩,⟨sg31822,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_635All : degreeTree43_635.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31831,⟨sg31827,⟨sg31825,⟨sg31824,True.intro,True.intro⟩,⟨sg31826,True.intro,True.intro⟩⟩,⟨sg31829,⟨sg31828,True.intro,True.intro⟩,⟨sg31830,True.intro,True.intro⟩⟩⟩,⟨sg31835,⟨sg31833,⟨sg31832,True.intro,True.intro⟩,⟨sg31834,True.intro,True.intro⟩⟩,⟨sg31837,⟨sg31836,True.intro,True.intro⟩,⟨sg31838,True.intro,True.intro⟩⟩⟩⟩

lemma degreeTree43_636All : degreeTree43_636.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31823,degreeTree43_634All,degreeTree43_635All⟩

lemma degreeTree43_637All : degreeTree43_637.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31855,⟨sg31847,⟨sg31843,⟨sg31841,⟨sg31840,True.intro,True.intro⟩,⟨sg31842,True.intro,True.intro⟩⟩,⟨sg31845,⟨sg31844,True.intro,True.intro⟩,⟨sg31846,True.intro,True.intro⟩⟩⟩,⟨sg31851,⟨sg31849,⟨sg31848,True.intro,True.intro⟩,⟨sg31850,True.intro,True.intro⟩⟩,⟨sg31853,⟨sg31852,True.intro,True.intro⟩,⟨sg31854,True.intro,True.intro⟩⟩⟩⟩,⟨sg31863,⟨sg31859,⟨sg31857,⟨sg31856,True.intro,True.intro⟩,⟨sg31858,True.intro,True.intro⟩⟩,⟨sg31861,⟨sg31860,True.intro,True.intro⟩,⟨sg31862,True.intro,True.intro⟩⟩⟩,⟨sg31867,⟨sg31865,⟨sg31864,True.intro,True.intro⟩,⟨sg31866,True.intro,True.intro⟩⟩,⟨sg31869,⟨sg31868,True.intro,True.intro⟩,⟨sg31870,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_638All : degreeTree43_638.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31839,degreeTree43_636All,degreeTree43_637All⟩

lemma degreeTree43_639All : degreeTree43_639.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31887,⟨sg31879,⟨sg31875,⟨sg31873,⟨sg31872,True.intro,True.intro⟩,⟨sg31874,True.intro,True.intro⟩⟩,⟨sg31877,⟨sg31876,True.intro,True.intro⟩,⟨sg31878,True.intro,True.intro⟩⟩⟩,⟨sg31883,⟨sg31881,⟨sg31880,True.intro,True.intro⟩,⟨sg31882,True.intro,True.intro⟩⟩,⟨sg31885,⟨sg31884,True.intro,True.intro⟩,⟨sg31886,True.intro,True.intro⟩⟩⟩⟩,⟨sg31895,⟨sg31891,⟨sg31889,⟨sg31888,True.intro,True.intro⟩,⟨sg31890,True.intro,True.intro⟩⟩,⟨sg31893,⟨sg31892,True.intro,True.intro⟩,⟨sg31894,True.intro,True.intro⟩⟩⟩,⟨sg31899,⟨sg31897,⟨sg31896,True.intro,True.intro⟩,⟨sg31898,True.intro,True.intro⟩⟩,⟨sg31901,⟨sg31900,True.intro,True.intro⟩,⟨sg31902,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_640All : degreeTree43_640.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31919,⟨sg31911,⟨sg31907,⟨sg31905,⟨sg31904,True.intro,True.intro⟩,⟨sg31906,True.intro,True.intro⟩⟩,⟨sg31909,⟨sg31908,True.intro,True.intro⟩,⟨sg31910,True.intro,True.intro⟩⟩⟩,⟨sg31915,⟨sg31913,⟨sg31912,True.intro,True.intro⟩,⟨sg31914,True.intro,True.intro⟩⟩,⟨sg31917,⟨sg31916,True.intro,True.intro⟩,⟨sg31918,True.intro,True.intro⟩⟩⟩⟩,⟨sg31927,⟨sg31923,⟨sg31921,⟨sg31920,True.intro,True.intro⟩,⟨sg31922,True.intro,True.intro⟩⟩,⟨sg31925,⟨sg31924,True.intro,True.intro⟩,⟨sg31926,True.intro,True.intro⟩⟩⟩,⟨sg31931,⟨sg31929,⟨sg31928,True.intro,True.intro⟩,⟨sg31930,True.intro,True.intro⟩⟩,⟨sg31933,⟨sg31932,True.intro,True.intro⟩,⟨sg31934,True.intro,True.intro⟩⟩⟩⟩⟩

lemma degreeTree43_641All : degreeTree43_641.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31903,degreeTree43_639All,degreeTree43_640All⟩

lemma degreeTree43_642All : degreeTree43_642.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31871,degreeTree43_638All,degreeTree43_641All⟩

lemma degreeTree43_643All : degreeTree43_643.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31806,degreeTree43_633All,degreeTree43_642All⟩

lemma degreeTree43_644All : degreeTree43_644.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31677,degreeTree43_624All,degreeTree43_643All⟩

lemma degreeTree43_645All : degreeTree43_645.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31419,degreeTree43_605All,degreeTree43_644All⟩

lemma degreeTree43_646All : degreeTree43_646.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg30903,degreeTree43_566All,degreeTree43_645All⟩

lemma degreeTree43_647All : degreeTree43_647.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg29870,degreeTree43_485All,degreeTree43_646All⟩

lemma degreeTree43_648All : degreeTree43_648.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg27805,degreeTree43_324All,degreeTree43_647All⟩

lemma degreeTreeAll43 : degreeTree43.All
    (fun rs => SquareOccurs (candidate 6 5 1) (rowDiagram rs)) := by
  have hp : rowDiagram [12,10,4,3,2,2,2,2,2,2,1,1] = candidate 6 5 1 := rowDiagram_candidate (M := 6) (b := 5) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree43_648All

end UniversalTensorSquare
end
end

end OAI
