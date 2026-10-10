import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes52
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes47
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes49
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes43
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes46
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes38
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes40
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes42
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes45

namespace OAI

/-! Semigroup Nodes 81. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32941 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,8,8,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20714 sg16237

lemma sg32942 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,8,8,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20715 sg16237

lemma sg32943 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,8,8,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16237

lemma sg32944 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,8,8,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20643 sg16670

lemma sg32945 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,8,8,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16704

lemma sg32946 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,8,8,8,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14313 sg21347

lemma sg32947 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,8,8,8,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20455

lemma sg32948 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,8,8,8,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20533 sg17181

lemma sg32949 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,8,8,8,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17245

lemma sg32950 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17555

lemma sg32951 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18310

lemma sg32952 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17555

lemma sg32953 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19722

lemma sg32954 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19722

lemma sg32955 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18310

lemma sg32956 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19722

lemma sg32957 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19722

lemma sg32958 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18310

lemma sg32959 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19722

lemma sg32960 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18310

lemma sg32961 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19722

lemma sg32962 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17316

lemma sg32963 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15773

lemma sg32964 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16353

lemma sg32965 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16762

lemma sg32966 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17316

lemma sg32967 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19616 sg19225

lemma sg32968 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19225

lemma sg32969 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17316

lemma sg32970 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19225

lemma sg32971 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19225

lemma sg32972 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18034

lemma sg32973 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16728

lemma sg32974 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18916 sg19631

lemma sg32975 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17275

lemma sg32976 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18917 sg19631

lemma sg32977 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17208

lemma sg32978 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17276

lemma sg32979 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19632

lemma sg32980 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17276

lemma sg32981 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18035

lemma sg32982 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16729

lemma sg32983 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18916 sg19632

lemma sg32984 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17276

lemma sg32985 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18917 sg19632

lemma sg32986 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16686

lemma sg32987 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16686

lemma sg32988 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20641 sg16686

lemma sg32989 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17209

lemma sg32990 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16283

lemma sg32991 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19187

lemma sg32992 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16264

lemma sg32993 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20803 sg16156

lemma sg32994 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20712 sg16264

lemma sg32995 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16687

lemma sg32996 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16687

lemma sg32997 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20641 sg16687

lemma sg32998 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17210

lemma sg32999 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16284

lemma sg33000 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19188

lemma sg33001 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16705

lemma sg33002 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17246

lemma sg33003 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16285

lemma sg33004 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17246

lemma sg33005 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16285

lemma sg33006 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17149 sg20552

lemma sg33007 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,7,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20720 sg16232

lemma sg33008 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16763

lemma sg33009 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16354

lemma sg33010 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17317

lemma sg33011 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15774

lemma sg33012 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16354

lemma sg33013 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16763

lemma sg33014 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17317

lemma sg33015 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19616 sg19226

lemma sg33016 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19226

lemma sg33017 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17317

lemma sg33018 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19226

lemma sg33019 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19226

lemma sg33020 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17277

lemma sg33021 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19633

lemma sg33022 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17277

lemma sg33023 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18036

lemma sg33024 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16730

lemma sg33025 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18916 sg19633

lemma sg33026 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17277

lemma sg33027 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18917 sg19633

lemma sg33028 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16688

lemma sg33029 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16688

lemma sg33030 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20641 sg16688

lemma sg33031 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17211

lemma sg33032 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16266

lemma sg33033 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20803 sg16158

lemma sg33034 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20712 sg16266

lemma sg33035 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16689

lemma sg33036 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16689

lemma sg33037 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20641 sg16689

lemma sg33038 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17212

lemma sg33039 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16286

lemma sg33040 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19189

lemma sg33041 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16706

lemma sg33042 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17249

lemma sg33043 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16287

lemma sg33044 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17249

lemma sg33045 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16287

lemma sg33046 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18287 sg20341

lemma sg33047 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16707

lemma sg33048 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17246

lemma sg33049 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17246

lemma sg33050 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17246

lemma sg33051 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16708

lemma sg33052 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,8,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20456

lemma sg33053 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,8,8,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17246

lemma sg33054 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17278

lemma sg33055 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15756

lemma sg33056 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20505 sg17278

lemma sg33057 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17278

lemma sg33058 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18284 sg20344

lemma sg33059 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17278

lemma sg33060 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18037

lemma sg33061 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16731

lemma sg33062 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18285 sg20344

lemma sg33063 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17278

lemma sg33064 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18286 sg20344

lemma sg33065 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16267

lemma sg33066 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20803 sg16159

lemma sg33067 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20712 sg16267

lemma sg33068 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16690

lemma sg33069 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16690

lemma sg33070 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20641 sg16690

lemma sg33071 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17213

lemma sg33072 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20721 sg16235

lemma sg33073 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20722 sg16235

lemma sg33074 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17249

lemma sg33075 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17249

lemma sg33076 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17249

lemma sg33077 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17248

lemma sg33078 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17248

lemma sg33079 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16709

lemma sg33080 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17249

lemma sg33081 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17249

lemma sg33082 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17249

lemma sg33083 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16710

lemma sg33084 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20457

lemma sg33085 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17249

lemma sg33086 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,8,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20533 sg17190

lemma sg33087 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18275 sg20421

lemma sg33088 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18137

lemma sg33089 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20323 sg18294

lemma sg33090 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16715

lemma sg33091 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20324 sg18294

lemma sg33092 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16715

lemma sg33093 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20325 sg18294

lemma sg33094 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16245

lemma sg33095 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20643 sg16673

lemma sg33096 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,7,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17252

lemma sg33097 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17556

lemma sg33098 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18311

lemma sg33099 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17556

lemma sg33100 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19723

lemma sg33101 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19723

lemma sg33102 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18311

lemma sg33103 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19723

lemma sg33104 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19723

lemma sg33105 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18311

lemma sg33106 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19723

lemma sg33107 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18311

lemma sg33108 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19723

lemma sg33109 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17341

lemma sg33110 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15790

lemma sg33111 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16375

lemma sg33112 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16785

lemma sg33113 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17341

lemma sg33114 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18932

lemma sg33115 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19236

lemma sg33116 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17341

lemma sg33117 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19236

lemma sg33118 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18932

lemma sg33119 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20696 sg16291

lemma sg33120 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16291

lemma sg33121 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20517 sg17258

lemma sg33122 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17264

lemma sg33123 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16718

lemma sg33124 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17264

lemma sg33125 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17266

lemma sg33126 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18139

lemma sg33127 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17266

lemma sg33128 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17265

lemma sg33129 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18138

lemma sg33130 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17265

lemma sg33131 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16290

lemma sg33132 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17257

lemma sg33133 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16719

lemma sg33134 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17265

lemma sg33135 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16719

lemma sg33136 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17265

lemma sg33137 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16291

lemma sg33138 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19190

lemma sg33139 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17266

lemma sg33140 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18139

lemma sg33141 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17266

lemma sg33142 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16720

lemma sg33143 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17266

lemma sg33144 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16720

lemma sg33145 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17266

lemma sg33146 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16292

lemma sg33147 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19191

lemma sg33148 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16712

lemma sg33149 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17148 sg20553

lemma sg33150 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16293

lemma sg33151 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20424 sg18137

lemma sg33152 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16293

lemma sg33153 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17149 sg20553

lemma sg33154 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,7,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20720 sg16245

lemma sg33155 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16786

lemma sg33156 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16376

lemma sg33157 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17342

lemma sg33158 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15791

lemma sg33159 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16376

lemma sg33160 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16786

lemma sg33161 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17342

lemma sg33162 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19576 sg19579

lemma sg33163 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19237

lemma sg33164 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17342

lemma sg33165 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19237

lemma sg33166 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19237

lemma sg33167 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17268

lemma sg33168 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18141

lemma sg33169 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17268

lemma sg33170 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17267

lemma sg33171 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18140

lemma sg33172 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17267

lemma sg33173 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20870 sg15710

lemma sg33174 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20715 sg16252

lemma sg33175 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16721

lemma sg33176 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17267

lemma sg33177 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16721

lemma sg33178 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17267

lemma sg33179 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17268

lemma sg33180 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18141

lemma sg33181 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17268

lemma sg33182 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16722

lemma sg33183 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17268

lemma sg33184 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16722

lemma sg33185 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17268

lemma sg33186 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16253

lemma sg33187 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20643 sg16679

lemma sg33188 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16713

lemma sg33189 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16254

lemma sg33190 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20807 sg16151

lemma sg33191 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20715 sg16254

lemma sg33192 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16254

lemma sg33193 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20643 sg16680

lemma sg33194 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16714

lemma sg33195 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18114 sg20458

lemma sg33196 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20326 sg18294

lemma sg33197 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20327 sg18294

lemma sg33198 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16715

lemma sg33199 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,8,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20458

lemma sg33200 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,8,8,8,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15613 sg21052

lemma sg33201 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18312

lemma sg33202 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg15750

lemma sg33203 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg20698 sg16294

lemma sg33204 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16379

lemma sg33205 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17557

lemma sg33206 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19724

lemma sg33207 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15792

lemma sg33208 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20693 sg16295

lemma sg33209 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20694 sg16295

lemma sg33210 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20695 sg16295

lemma sg33211 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19724

lemma sg33212 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18312

lemma sg33213 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19724

lemma sg33214 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19724

lemma sg33215 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18312

lemma sg33216 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19724

lemma sg33217 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18312

lemma sg33218 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19724

lemma sg33219 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19575 sg19609

lemma sg33220 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17343

lemma sg33221 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20319 sg18298

lemma sg33222 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20320 sg18298

lemma sg33223 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16469

lemma sg33224 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18313

lemma sg33225 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16788

lemma sg33226 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16378

lemma sg33227 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg15752

lemma sg33228 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17269

lemma sg33229 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18142

lemma sg33230 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17269

lemma sg33231 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17558

lemma sg33232 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19725

lemma sg33233 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19725

lemma sg33234 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18313

lemma sg33235 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19725

lemma sg33236 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19725

lemma sg33237 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18313

lemma sg33238 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19725

lemma sg33239 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18313

lemma sg33240 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19725

lemma sg33241 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16788

lemma sg33242 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17344

lemma sg33243 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18933

lemma sg33244 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19238

lemma sg33245 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17344

lemma sg33246 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19238

lemma sg33247 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18933

lemma sg33248 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20718 sg16246

lemma sg33249 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20789 sg16192

lemma sg33250 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17345

lemma sg33251 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15794

lemma sg33252 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16379

lemma sg33253 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16789

lemma sg33254 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17345

lemma sg33255 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18934

lemma sg33256 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19239

lemma sg33257 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17345

lemma sg33258 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19239

lemma sg33259 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18934

lemma sg33260 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17271

lemma sg33261 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18143

lemma sg33262 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17271

lemma sg33263 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17270

lemma sg33264 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16723

lemma sg33265 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17270

lemma sg33266 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16724

lemma sg33267 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17271

lemma sg33268 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16724

lemma sg33269 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17271

lemma sg33270 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17559

lemma sg33271 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18314

lemma sg33272 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17559

lemma sg33273 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19726

lemma sg33274 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19726

lemma sg33275 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18314

lemma sg33276 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19726

lemma sg33277 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19726

lemma sg33278 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18314

lemma sg33279 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19726

lemma sg33280 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18314

lemma sg33281 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19726

lemma sg33282 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17346

lemma sg33283 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15795

lemma sg33284 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16380

lemma sg33285 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16790

lemma sg33286 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17346

lemma sg33287 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18935

lemma sg33288 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19240

lemma sg33289 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17346

lemma sg33290 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19240

lemma sg33291 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18935

lemma sg33292 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20696 sg16298

lemma sg33293 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16298

lemma sg33294 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20517 sg17262

lemma sg33295 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17272

lemma sg33296 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16725

lemma sg33297 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17272

lemma sg33298 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17274

lemma sg33299 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18145

lemma sg33300 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17274

lemma sg33301 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17273

lemma sg33302 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18144

lemma sg33303 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17273

lemma sg33304 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16297

lemma sg33305 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17261

lemma sg33306 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16726

lemma sg33307 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17273

lemma sg33308 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16726

lemma sg33309 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17273

lemma sg33310 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16298

lemma sg33311 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19192

lemma sg33312 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17274

lemma sg33313 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18145

lemma sg33314 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17274

lemma sg33315 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16727

lemma sg33316 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17274

lemma sg33317 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16727

lemma sg33318 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17274

lemma sg33319 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16299

lemma sg33320 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19193

lemma sg33321 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20720 sg16247

lemma sg33322 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16791

lemma sg33323 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16381

lemma sg33324 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17347

lemma sg33325 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15796

lemma sg33326 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16381

lemma sg33327 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16791

lemma sg33328 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17347

lemma sg33329 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18936

lemma sg33330 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19241

lemma sg33331 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17347

lemma sg33332 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19241

lemma sg33333 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18936

lemma sg33334 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17276

lemma sg33335 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18147

lemma sg33336 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17276

lemma sg33337 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17275

lemma sg33338 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18146

lemma sg33339 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17275

lemma sg33340 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,7,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16300

end UniversalTensorSquare
end
end

end OAI
