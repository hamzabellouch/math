import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Finite.DegreeTreeData24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes28
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes29

namespace OAI

/-! Degree Tree Proof 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree24_0All : degreeTree24_0.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11856,⟨sg11848,⟨sg11844,⟨sg11842,⟨sg11841,True.intro,True.intro⟩,⟨sg11843,True.intro,True.intro⟩⟩,⟨sg11846,⟨sg11845,True.intro,True.intro⟩,⟨sg11847,True.intro,True.intro⟩⟩⟩,⟨sg11852,⟨sg11850,⟨sg11849,True.intro,True.intro⟩,⟨sg11851,True.intro,True.intro⟩⟩,⟨sg11854,⟨sg11853,True.intro,True.intro⟩,⟨sg11855,True.intro,True.intro⟩⟩⟩⟩,⟨sg11864,⟨sg11860,⟨sg11858,⟨sg11857,True.intro,True.intro⟩,⟨sg11859,True.intro,True.intro⟩⟩,⟨sg11862,⟨sg11861,True.intro,True.intro⟩,⟨sg11863,True.intro,True.intro⟩⟩⟩,⟨sg11868,⟨sg11866,⟨sg11865,True.intro,True.intro⟩,⟨sg11867,True.intro,True.intro⟩⟩,⟨sg11870,⟨sg11869,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_1All : degreeTree24_1.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11887,⟨sg11879,⟨sg11875,⟨sg11873,⟨sg11872,True.intro,True.intro⟩,⟨sg11874,True.intro,True.intro⟩⟩,⟨sg11877,⟨sg11876,True.intro,True.intro⟩,⟨sg11878,True.intro,True.intro⟩⟩⟩,⟨sg11883,⟨sg11881,⟨sg11880,True.intro,True.intro⟩,⟨sg11882,True.intro,True.intro⟩⟩,⟨sg11885,⟨sg11884,True.intro,True.intro⟩,⟨sg11886,True.intro,True.intro⟩⟩⟩⟩,⟨sg11895,⟨sg11891,⟨sg11889,⟨sg11888,True.intro,True.intro⟩,⟨sg11890,True.intro,True.intro⟩⟩,⟨sg11893,⟨sg11892,True.intro,True.intro⟩,⟨sg11894,True.intro,True.intro⟩⟩⟩,⟨sg11899,⟨sg11897,⟨sg11896,True.intro,True.intro⟩,⟨sg11898,True.intro,True.intro⟩⟩,⟨sg11901,⟨sg11900,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_2All : degreeTree24_2.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11871,degreeTree24_0All,degreeTree24_1All⟩

lemma degreeTree24_3All : degreeTree24_3.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11918,⟨sg11910,⟨sg11906,⟨sg11904,⟨sg11903,True.intro,True.intro⟩,⟨sg11905,True.intro,True.intro⟩⟩,⟨sg11908,⟨sg11907,True.intro,True.intro⟩,⟨sg11909,True.intro,True.intro⟩⟩⟩,⟨sg11914,⟨sg11912,⟨sg11911,True.intro,True.intro⟩,⟨sg11913,True.intro,True.intro⟩⟩,⟨sg11916,⟨sg11915,True.intro,True.intro⟩,⟨sg11917,True.intro,True.intro⟩⟩⟩⟩,⟨sg11926,⟨sg11922,⟨sg11920,⟨sg11919,True.intro,True.intro⟩,⟨sg11921,True.intro,True.intro⟩⟩,⟨sg11924,⟨sg11923,True.intro,True.intro⟩,⟨sg11925,True.intro,True.intro⟩⟩⟩,⟨sg11930,⟨sg11928,⟨sg11927,True.intro,True.intro⟩,⟨sg11929,True.intro,True.intro⟩⟩,⟨sg11932,⟨sg11931,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_4All : degreeTree24_4.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11948,⟨sg11941,⟨sg11937,⟨sg11935,⟨sg11934,True.intro,True.intro⟩,⟨sg11936,True.intro,True.intro⟩⟩,⟨sg11939,⟨sg11938,True.intro,True.intro⟩,⟨sg11940,True.intro,True.intro⟩⟩⟩,⟨sg11945,⟨sg11943,⟨sg11942,True.intro,True.intro⟩,⟨sg11944,True.intro,True.intro⟩⟩,⟨sg11947,⟨sg11946,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg11956,⟨sg11952,⟨sg11950,⟨sg11949,True.intro,True.intro⟩,⟨sg11951,True.intro,True.intro⟩⟩,⟨sg11954,⟨sg11953,True.intro,True.intro⟩,⟨sg11955,True.intro,True.intro⟩⟩⟩,⟨sg11960,⟨sg11958,⟨sg11957,True.intro,True.intro⟩,⟨sg11959,True.intro,True.intro⟩⟩,⟨sg11962,⟨sg11961,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_5All : degreeTree24_5.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11933,degreeTree24_3All,degreeTree24_4All⟩

lemma degreeTree24_6All : degreeTree24_6.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11902,degreeTree24_2All,degreeTree24_5All⟩

lemma degreeTree24_7All : degreeTree24_7.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11979,⟨sg11971,⟨sg11967,⟨sg11965,⟨sg11964,True.intro,True.intro⟩,⟨sg11966,True.intro,True.intro⟩⟩,⟨sg11969,⟨sg11968,True.intro,True.intro⟩,⟨sg11970,True.intro,True.intro⟩⟩⟩,⟨sg11975,⟨sg11973,⟨sg11972,True.intro,True.intro⟩,⟨sg11974,True.intro,True.intro⟩⟩,⟨sg11977,⟨sg11976,True.intro,True.intro⟩,⟨sg11978,True.intro,True.intro⟩⟩⟩⟩,⟨sg11987,⟨sg11983,⟨sg11981,⟨sg11980,True.intro,True.intro⟩,⟨sg11982,True.intro,True.intro⟩⟩,⟨sg11985,⟨sg11984,True.intro,True.intro⟩,⟨sg11986,True.intro,True.intro⟩⟩⟩,⟨sg11991,⟨sg11989,⟨sg11988,True.intro,True.intro⟩,⟨sg11990,True.intro,True.intro⟩⟩,⟨sg11993,⟨sg11992,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_8All : degreeTree24_8.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12010,⟨sg12002,⟨sg11998,⟨sg11996,⟨sg11995,True.intro,True.intro⟩,⟨sg11997,True.intro,True.intro⟩⟩,⟨sg12000,⟨sg11999,True.intro,True.intro⟩,⟨sg12001,True.intro,True.intro⟩⟩⟩,⟨sg12006,⟨sg12004,⟨sg12003,True.intro,True.intro⟩,⟨sg12005,True.intro,True.intro⟩⟩,⟨sg12008,⟨sg12007,True.intro,True.intro⟩,⟨sg12009,True.intro,True.intro⟩⟩⟩⟩,⟨sg12018,⟨sg12014,⟨sg12012,⟨sg12011,True.intro,True.intro⟩,⟨sg12013,True.intro,True.intro⟩⟩,⟨sg12016,⟨sg12015,True.intro,True.intro⟩,⟨sg12017,True.intro,True.intro⟩⟩⟩,⟨sg12022,⟨sg12020,⟨sg12019,True.intro,True.intro⟩,⟨sg12021,True.intro,True.intro⟩⟩,⟨sg12024,⟨sg12023,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_9All : degreeTree24_9.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11994,degreeTree24_7All,degreeTree24_8All⟩

lemma degreeTree24_10All : degreeTree24_10.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12041,⟨sg12033,⟨sg12029,⟨sg12027,⟨sg12026,True.intro,True.intro⟩,⟨sg12028,True.intro,True.intro⟩⟩,⟨sg12031,⟨sg12030,True.intro,True.intro⟩,⟨sg12032,True.intro,True.intro⟩⟩⟩,⟨sg12037,⟨sg12035,⟨sg12034,True.intro,True.intro⟩,⟨sg12036,True.intro,True.intro⟩⟩,⟨sg12039,⟨sg12038,True.intro,True.intro⟩,⟨sg12040,True.intro,True.intro⟩⟩⟩⟩,⟨sg12049,⟨sg12045,⟨sg12043,⟨sg12042,True.intro,True.intro⟩,⟨sg12044,True.intro,True.intro⟩⟩,⟨sg12047,⟨sg12046,True.intro,True.intro⟩,⟨sg12048,True.intro,True.intro⟩⟩⟩,⟨sg12053,⟨sg12051,⟨sg12050,True.intro,True.intro⟩,⟨sg12052,True.intro,True.intro⟩⟩,⟨sg12055,⟨sg12054,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_11All : degreeTree24_11.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12071,⟨sg12064,⟨sg12060,⟨sg12058,⟨sg12057,True.intro,True.intro⟩,⟨sg12059,True.intro,True.intro⟩⟩,⟨sg12062,⟨sg12061,True.intro,True.intro⟩,⟨sg12063,True.intro,True.intro⟩⟩⟩,⟨sg12068,⟨sg12066,⟨sg12065,True.intro,True.intro⟩,⟨sg12067,True.intro,True.intro⟩⟩,⟨sg12070,⟨sg12069,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg12079,⟨sg12075,⟨sg12073,⟨sg12072,True.intro,True.intro⟩,⟨sg12074,True.intro,True.intro⟩⟩,⟨sg12077,⟨sg12076,True.intro,True.intro⟩,⟨sg12078,True.intro,True.intro⟩⟩⟩,⟨sg12083,⟨sg12081,⟨sg12080,True.intro,True.intro⟩,⟨sg12082,True.intro,True.intro⟩⟩,⟨sg12085,⟨sg12084,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_12All : degreeTree24_12.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12056,degreeTree24_10All,degreeTree24_11All⟩

lemma degreeTree24_13All : degreeTree24_13.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12025,degreeTree24_9All,degreeTree24_12All⟩

lemma degreeTree24_14All : degreeTree24_14.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg11963,degreeTree24_6All,degreeTree24_13All⟩

lemma degreeTree24_15All : degreeTree24_15.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12102,⟨sg12094,⟨sg12090,⟨sg12088,⟨sg12087,True.intro,True.intro⟩,⟨sg12089,True.intro,True.intro⟩⟩,⟨sg12092,⟨sg12091,True.intro,True.intro⟩,⟨sg12093,True.intro,True.intro⟩⟩⟩,⟨sg12098,⟨sg12096,⟨sg12095,True.intro,True.intro⟩,⟨sg12097,True.intro,True.intro⟩⟩,⟨sg12100,⟨sg12099,True.intro,True.intro⟩,⟨sg12101,True.intro,True.intro⟩⟩⟩⟩,⟨sg12110,⟨sg12106,⟨sg12104,⟨sg12103,True.intro,True.intro⟩,⟨sg12105,True.intro,True.intro⟩⟩,⟨sg12108,⟨sg12107,True.intro,True.intro⟩,⟨sg12109,True.intro,True.intro⟩⟩⟩,⟨sg12114,⟨sg12112,⟨sg12111,True.intro,True.intro⟩,⟨sg12113,True.intro,True.intro⟩⟩,⟨sg12116,⟨sg12115,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_16All : degreeTree24_16.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12133,⟨sg12125,⟨sg12121,⟨sg12119,⟨sg12118,True.intro,True.intro⟩,⟨sg12120,True.intro,True.intro⟩⟩,⟨sg12123,⟨sg12122,True.intro,True.intro⟩,⟨sg12124,True.intro,True.intro⟩⟩⟩,⟨sg12129,⟨sg12127,⟨sg12126,True.intro,True.intro⟩,⟨sg12128,True.intro,True.intro⟩⟩,⟨sg12131,⟨sg12130,True.intro,True.intro⟩,⟨sg12132,True.intro,True.intro⟩⟩⟩⟩,⟨sg12141,⟨sg12137,⟨sg12135,⟨sg12134,True.intro,True.intro⟩,⟨sg12136,True.intro,True.intro⟩⟩,⟨sg12139,⟨sg12138,True.intro,True.intro⟩,⟨sg12140,True.intro,True.intro⟩⟩⟩,⟨sg12145,⟨sg12143,⟨sg12142,True.intro,True.intro⟩,⟨sg12144,True.intro,True.intro⟩⟩,⟨sg12147,⟨sg12146,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_17All : degreeTree24_17.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12117,degreeTree24_15All,degreeTree24_16All⟩

lemma degreeTree24_18All : degreeTree24_18.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12164,⟨sg12156,⟨sg12152,⟨sg12150,⟨sg12149,True.intro,True.intro⟩,⟨sg12151,True.intro,True.intro⟩⟩,⟨sg12154,⟨sg12153,True.intro,True.intro⟩,⟨sg12155,True.intro,True.intro⟩⟩⟩,⟨sg12160,⟨sg12158,⟨sg12157,True.intro,True.intro⟩,⟨sg12159,True.intro,True.intro⟩⟩,⟨sg12162,⟨sg12161,True.intro,True.intro⟩,⟨sg12163,True.intro,True.intro⟩⟩⟩⟩,⟨sg12172,⟨sg12168,⟨sg12166,⟨sg12165,True.intro,True.intro⟩,⟨sg12167,True.intro,True.intro⟩⟩,⟨sg12170,⟨sg12169,True.intro,True.intro⟩,⟨sg12171,True.intro,True.intro⟩⟩⟩,⟨sg12176,⟨sg12174,⟨sg12173,True.intro,True.intro⟩,⟨sg12175,True.intro,True.intro⟩⟩,⟨sg12178,⟨sg12177,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_19All : degreeTree24_19.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12194,⟨sg12187,⟨sg12183,⟨sg12181,⟨sg12180,True.intro,True.intro⟩,⟨sg12182,True.intro,True.intro⟩⟩,⟨sg12185,⟨sg12184,True.intro,True.intro⟩,⟨sg12186,True.intro,True.intro⟩⟩⟩,⟨sg12191,⟨sg12189,⟨sg12188,True.intro,True.intro⟩,⟨sg12190,True.intro,True.intro⟩⟩,⟨sg12193,⟨sg12192,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg12202,⟨sg12198,⟨sg12196,⟨sg12195,True.intro,True.intro⟩,⟨sg12197,True.intro,True.intro⟩⟩,⟨sg12200,⟨sg12199,True.intro,True.intro⟩,⟨sg12201,True.intro,True.intro⟩⟩⟩,⟨sg12206,⟨sg12204,⟨sg12203,True.intro,True.intro⟩,⟨sg12205,True.intro,True.intro⟩⟩,⟨sg12208,⟨sg12207,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_20All : degreeTree24_20.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12179,degreeTree24_18All,degreeTree24_19All⟩

lemma degreeTree24_21All : degreeTree24_21.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12148,degreeTree24_17All,degreeTree24_20All⟩

lemma degreeTree24_22All : degreeTree24_22.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12225,⟨sg12217,⟨sg12213,⟨sg12211,⟨sg12210,True.intro,True.intro⟩,⟨sg12212,True.intro,True.intro⟩⟩,⟨sg12215,⟨sg12214,True.intro,True.intro⟩,⟨sg12216,True.intro,True.intro⟩⟩⟩,⟨sg12221,⟨sg12219,⟨sg12218,True.intro,True.intro⟩,⟨sg12220,True.intro,True.intro⟩⟩,⟨sg12223,⟨sg12222,True.intro,True.intro⟩,⟨sg12224,True.intro,True.intro⟩⟩⟩⟩,⟨sg12233,⟨sg12229,⟨sg12227,⟨sg12226,True.intro,True.intro⟩,⟨sg12228,True.intro,True.intro⟩⟩,⟨sg12231,⟨sg12230,True.intro,True.intro⟩,⟨sg12232,True.intro,True.intro⟩⟩⟩,⟨sg12237,⟨sg12235,⟨sg12234,True.intro,True.intro⟩,⟨sg12236,True.intro,True.intro⟩⟩,⟨sg12239,⟨sg12238,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_23All : degreeTree24_23.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12255,⟨sg12248,⟨sg12244,⟨sg12242,⟨sg12241,True.intro,True.intro⟩,⟨sg12243,True.intro,True.intro⟩⟩,⟨sg12246,⟨sg12245,True.intro,True.intro⟩,⟨sg12247,True.intro,True.intro⟩⟩⟩,⟨sg12252,⟨sg12250,⟨sg12249,True.intro,True.intro⟩,⟨sg12251,True.intro,True.intro⟩⟩,⟨sg12254,⟨sg12253,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg12263,⟨sg12259,⟨sg12257,⟨sg12256,True.intro,True.intro⟩,⟨sg12258,True.intro,True.intro⟩⟩,⟨sg12261,⟨sg12260,True.intro,True.intro⟩,⟨sg12262,True.intro,True.intro⟩⟩⟩,⟨sg12267,⟨sg12265,⟨sg12264,True.intro,True.intro⟩,⟨sg12266,True.intro,True.intro⟩⟩,⟨sg12269,⟨sg12268,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_24All : degreeTree24_24.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12240,degreeTree24_22All,degreeTree24_23All⟩

lemma degreeTree24_25All : degreeTree24_25.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12286,⟨sg12278,⟨sg12274,⟨sg12272,⟨sg12271,True.intro,True.intro⟩,⟨sg12273,True.intro,True.intro⟩⟩,⟨sg12276,⟨sg12275,True.intro,True.intro⟩,⟨sg12277,True.intro,True.intro⟩⟩⟩,⟨sg12282,⟨sg12280,⟨sg12279,True.intro,True.intro⟩,⟨sg12281,True.intro,True.intro⟩⟩,⟨sg12284,⟨sg12283,True.intro,True.intro⟩,⟨sg12285,True.intro,True.intro⟩⟩⟩⟩,⟨sg12294,⟨sg12290,⟨sg12288,⟨sg12287,True.intro,True.intro⟩,⟨sg12289,True.intro,True.intro⟩⟩,⟨sg12292,⟨sg12291,True.intro,True.intro⟩,⟨sg12293,True.intro,True.intro⟩⟩⟩,⟨sg12298,⟨sg12296,⟨sg12295,True.intro,True.intro⟩,⟨sg12297,True.intro,True.intro⟩⟩,⟨sg12300,⟨sg12299,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_26All : degreeTree24_26.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12316,⟨sg12309,⟨sg12305,⟨sg12303,⟨sg12302,True.intro,True.intro⟩,⟨sg12304,True.intro,True.intro⟩⟩,⟨sg12307,⟨sg12306,True.intro,True.intro⟩,⟨sg12308,True.intro,True.intro⟩⟩⟩,⟨sg12313,⟨sg12311,⟨sg12310,True.intro,True.intro⟩,⟨sg12312,True.intro,True.intro⟩⟩,⟨sg12315,⟨sg12314,True.intro,True.intro⟩,True.intro⟩⟩⟩,⟨sg12324,⟨sg12320,⟨sg12318,⟨sg12317,True.intro,True.intro⟩,⟨sg12319,True.intro,True.intro⟩⟩,⟨sg12322,⟨sg12321,True.intro,True.intro⟩,⟨sg12323,True.intro,True.intro⟩⟩⟩,⟨sg12328,⟨sg12326,⟨sg12325,True.intro,True.intro⟩,⟨sg12327,True.intro,True.intro⟩⟩,⟨sg12330,⟨sg12329,True.intro,True.intro⟩,True.intro⟩⟩⟩⟩

lemma degreeTree24_27All : degreeTree24_27.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12301,degreeTree24_25All,degreeTree24_26All⟩

lemma degreeTree24_28All : degreeTree24_28.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12270,degreeTree24_24All,degreeTree24_27All⟩

lemma degreeTree24_29All : degreeTree24_29.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12209,degreeTree24_21All,degreeTree24_28All⟩

lemma degreeTree24_30All : degreeTree24_30.All (RowSquare [8,6,2,2,2,2,1,1]) := by
  exact ⟨sg12086,degreeTree24_14All,degreeTree24_29All⟩

lemma degreeTreeAll24 : degreeTree24.All
    (fun rs => SquareOccurs (candidate 4 3 1) (rowDiagram rs)) := by
  have hp : rowDiagram [8,6,2,2,2,2,1,1] = candidate 4 3 1 := rowDiagram_candidate (M := 4) (b := 3) (δ := 1) (by decide)
  rw [← hp]
  exact degreeTree24_30All

end UniversalTensorSquare
end
end

end OAI
