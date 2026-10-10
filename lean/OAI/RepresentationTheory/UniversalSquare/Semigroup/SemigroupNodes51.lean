import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes50

namespace OAI

/-! Semigroup Nodes 51. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg20940 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1474 sg8780

lemma sg20941 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [7,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1475 sg8780

lemma sg20942 : RowSquare [6,6,3,3,2,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1476 sg8780

lemma sg20943 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg5764

lemma sg20944 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg5765

lemma sg20945 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3334 sg4941

lemma sg20946 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4949

lemma sg20947 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3323 sg4958

lemma sg20948 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3332 sg4944

lemma sg20949 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3332 sg4945

lemma sg20950 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,4] := by
  exact rowSquare_join (by decide) sg3332 sg4949

lemma sg20951 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1,1] := by
  exact rowSquare_join (by decide) sg3334 sg4948

lemma sg20952 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,4] := by
  exact rowSquare_join (by decide) sg3332 sg4956

lemma sg20953 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,6] := by
  exact rowSquare_join (by decide) sg3732 sg4844

lemma sg20954 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3407 sg4897

lemma sg20955 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3330 sg4959

lemma sg20956 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4963

lemma sg20957 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3332 sg4959

lemma sg20958 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,3] := by
  exact rowSquare_join (by decide) sg3332 sg4960

lemma sg20959 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1757 sg8002

lemma sg20960 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,8,8] := by
  exact rowSquare_join (by decide) sg1675 sg8015

lemma sg20961 : RowSquare [7,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4167 sg4402

lemma sg20962 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [4,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg11531

lemma sg20963 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [5,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg984 sg10868

lemma sg20964 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg661 sg11531

lemma sg20965 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg662 sg11531

lemma sg20966 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg985 sg10869

lemma sg20967 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg991 sg10867

lemma sg20968 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg663 sg11531

lemma sg20969 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg992 sg10867

lemma sg20970 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg987 sg10868

lemma sg20971 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg664 sg11531

lemma sg20972 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg988 sg10868

lemma sg20973 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg665 sg11531

lemma sg20974 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg989 sg10868

lemma sg20975 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg666 sg11531

lemma sg20976 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg10867

lemma sg20977 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg667 sg11531

lemma sg20978 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg994 sg10867

lemma sg20979 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg991 sg10868

lemma sg20980 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg668 sg11531

lemma sg20981 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg992 sg10868

lemma sg20982 : RowSquare [7,6,3,2,2,2,2,2,2,2,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg669 sg11531

lemma sg20983 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3332 sg4935

lemma sg20984 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3593 sg4875

lemma sg20985 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,4] := by
  exact rowSquare_join (by decide) sg4378 sg4173

lemma sg20986 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,4] := by
  exact rowSquare_join (by decide) sg13 sg14653

lemma sg20987 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14655

lemma sg20988 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14667

lemma sg20989 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,4] := by
  exact rowSquare_join (by decide) sg14 sg14653

lemma sg20990 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,3] := by
  exact rowSquare_join (by decide) sg295 sg11598

lemma sg20991 : RowSquare [7,6,4,3,3,2,1,1,1,1,1,1,1] [6,6,6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11715

lemma sg20992 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [5,5,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg402 sg11798

lemma sg20993 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [5,5,3,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg402 sg11799

lemma sg20994 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [5,5,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg402 sg11800

lemma sg20995 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg403 sg11799

lemma sg20996 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg403 sg11800

lemma sg20997 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11798

lemma sg20998 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11799

lemma sg20999 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11800

lemma sg21000 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg408 sg11795

lemma sg21001 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg409 sg11795

lemma sg21002 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg408 sg11796

lemma sg21003 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg408 sg11797

lemma sg21004 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg410 sg11795

lemma sg21005 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg409 sg11796

lemma sg21006 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg409 sg11797

lemma sg21007 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg404 sg11803

lemma sg21008 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg405 sg11803

lemma sg21009 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,4,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg405 sg11804

lemma sg21010 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg410 sg11796

lemma sg21011 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg410 sg11797

lemma sg21012 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,5,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg410 sg11798

lemma sg21013 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg406 sg11803

lemma sg21014 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11802

lemma sg21015 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg402 sg11812

lemma sg21016 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11803

lemma sg21017 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,6,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11804

lemma sg21018 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11806

lemma sg21019 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11807

lemma sg21020 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11808

lemma sg21021 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg411 sg11795

lemma sg21022 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg412 sg11795

lemma sg21023 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg411 sg11796

lemma sg21024 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg411 sg11797

lemma sg21025 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg408 sg11803

lemma sg21026 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg412 sg11796

lemma sg21027 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg412 sg11797

lemma sg21028 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg409 sg11803

lemma sg21029 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg410 sg11803

lemma sg21030 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg410 sg11804

lemma sg21031 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,5,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg410 sg11805

lemma sg21032 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11812

lemma sg21033 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11813

lemma sg21034 : RowSquare [7,7,2,2,2,2,2,2,2,2,1,1] [8,8,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11815

lemma sg21035 : RowSquare [7,7,3,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3316 sg4936

lemma sg21036 : RowSquare [7,7,3,2,2,2,2,2,2,2,1] [7,7,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg11809

lemma sg21037 : RowSquare [7,7,3,2,2,2,2,2,2,2,1] [7,7,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg363 sg11810

lemma sg21038 : RowSquare [7,7,3,2,2,2,2,2,2,2,1] [8,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg11814

lemma sg21039 : RowSquare [7,7,3,2,2,2,2,2,2,2,1] [8,8,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg11815

lemma sg21040 : RowSquare [7,7,3,3,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg5749

lemma sg21041 : RowSquare [8,6,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14705

lemma sg21042 : RowSquare [8,6,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14706

lemma sg21043 : RowSquare [8,6,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14707

lemma sg21044 : RowSquare [8,6,3,3,3,2,1,1,1,1,1,1,1] [6,5,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg2135 sg6488

lemma sg21045 : RowSquare [8,6,4,3,2,2,1,1,1,1,1,1,1] [6,5,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg74 sg12863

lemma sg21046 : RowSquare [8,6,4,3,2,2,1,1,1,1,1,1,1] [6,6,5,5,5,5] := by
  exact rowSquare_join (by decide) sg74 sg12864

lemma sg21047 : RowSquare [8,6,4,3,2,2,1,1,1,1,1,1,1] [7,5,5,5,5,5] := by
  exact rowSquare_join (by decide) sg74 sg12865

lemma sg21048 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg5744

lemma sg21049 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg5745

lemma sg21050 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg5737

lemma sg21051 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg5738

lemma sg21052 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2710 sg5738

lemma sg21053 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,4] := by
  exact rowSquare_join (by decide) sg74 sg13504

lemma sg21054 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,4] := by
  exact rowSquare_join (by decide) sg74 sg13508

lemma sg21055 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14709

lemma sg21056 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14710

lemma sg21057 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14711

lemma sg21058 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14712

lemma sg21059 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14713

lemma sg21060 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,6,2,2] := by
  exact rowSquare_join (by decide) sg358 sg11613

lemma sg21061 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,7,7,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11601

lemma sg21062 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,8] := by
  exact rowSquare_join (by decide) sg364 sg11602

lemma sg21063 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,3] := by
  exact rowSquare_join (by decide) sg356 sg11679

lemma sg21064 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg281 sg11726

lemma sg21065 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg356 sg11709

lemma sg21066 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,3,3,3,3] := by
  exact rowSquare_join (by decide) sg356 sg11710

lemma sg21067 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11603

lemma sg21068 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,10,4,4,2,2] := by
  exact rowSquare_join (by decide) sg356 sg11711

lemma sg21069 : RowSquare [8,7,3,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg14530

lemma sg21070 : RowSquare [8,7,3,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg14531

lemma sg21071 : RowSquare [8,7,3,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg43 sg14532

lemma sg21072 : RowSquare [8,7,3,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg14529

lemma sg21073 : RowSquare [8,7,3,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg14530

lemma sg21074 : RowSquare [8,7,3,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg14531

lemma sg21075 : RowSquare [8,7,3,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg44 sg14532

lemma sg21076 : RowSquare [8,7,3,3,2,2,1,1,1,1,1,1,1] [5,5,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2589 sg5738

lemma sg21077 : RowSquare [8,8,3,2,2,2,1,1,1,1,1,1,1] [6,6,6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg364 sg11715

lemma sg21078 : RowSquare [8,8,3,2,2,2,1,1,1,1,1,1,1] [7,7,7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11716

lemma sg21079 : RowSquare [8,8,3,2,2,2,1,1,1,1,1,1,1] [8,8,8,8] := by
  exact rowSquare_join (by decide) sg364 sg11717

lemma sg21080 : RowSquare [9,7,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg14808

lemma sg21081 : RowSquare [9,7,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg14809

lemma sg21082 : RowSquare [9,7,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15 sg14810

lemma sg21083 : RowSquare [9,7,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg14811

lemma sg21084 : RowSquare [9,7,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2590 sg5760

lemma sg21085 : RowSquare [9,7,3,3,2,1,1,1,1,1,1,1,1] [7,7,7,7,2,2] := by
  exact rowSquare_join (by decide) sg960 sg8921

lemma sg21086 : RowSquare [9,7,3,3,2,1,1,1,1,1,1,1,1] [8,8,6,6,2,2] := by
  exact rowSquare_join (by decide) sg960 sg8932

lemma sg21087 : RowSquare [9,7,3,3,2,1,1,1,1,1,1,1,1] [8,8,7,7,1,1] := by
  exact rowSquare_join (by decide) sg960 sg8933

lemma sg21088 : RowSquare [9,7,3,3,2,1,1,1,1,1,1,1,1] [8,8,8,3,3,2] := by
  exact rowSquare_join (by decide) sg563 sg11199

lemma sg21089 : RowSquare [9,7,3,3,2,1,1,1,1,1,1,1,1] [8,8,8,8] := by
  exact rowSquare_join (by decide) sg364 sg11718

lemma sg21090 : RowSquare [9,8,2,2,2,2,1,1,1,1,1,1,1] [4,4,4,4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2546 sg5760

lemma sg21091 : RowSquare [9,8,3,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2529 sg5760

lemma sg21092 : RowSquare [9,9,2,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14775

lemma sg21093 : RowSquare [9,9,2,2,2,2,2,2,2] [4,4,4,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3220 sg4816

lemma sg21094 : RowSquare [9,9,2,2,2,2,2,2,2] [4,4,4,4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3220 sg4812

lemma sg21095 : RowSquare [9,9,2,2,2,2,2,2,2] [4,4,4,4,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3220 sg4815

lemma sg21096 : RowSquare [9,9,2,2,2,2,2,2,2] [4,4,4,4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3220 sg4811

lemma sg21097 : RowSquare [9,9,2,2,2,2,2,2,2] [4,4,4,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3220 sg4813

lemma sg21098 : RowSquare [9,9,2,2,2,2,2,2,2] [4,4,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3225 sg4810

lemma sg21099 : RowSquare [9,9,2,2,2,2,2,2,2] [4,4,4,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3223 sg4810

lemma sg21100 : RowSquare [9,9,2,2,2,2,2,2,2] [4,4,4,4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3220 sg4810

lemma sg21101 : RowSquare [10,8,2,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4060 sg3910

lemma sg21102 : RowSquare [10,8,2,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4060 sg3909

lemma sg21103 : RowSquare [10,8,2,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4060 sg3908

lemma sg21104 : RowSquare [10,8,2,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4060 sg3907

lemma sg21105 : RowSquare [10,8,2,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4060 sg3906

lemma sg21106 : RowSquare [10,8,2,2,2,2,2,2,1,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4060 sg3905

lemma sg21107 : RowSquare [7,6,3,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg991 sg11531

lemma sg21108 : RowSquare [7,6,3,3,2,2,2,2,2,2,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg11531

lemma sg21109 : RowSquare [7,6,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg990 sg11532

lemma sg21110 : RowSquare [7,6,3,3,2,2,2,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg994 sg11531

lemma sg21111 : RowSquare [7,6,3,3,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg11532

lemma sg21112 : RowSquare [7,6,4,3,2,2,2,2,2,2,1] [6,6,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg12649

lemma sg21113 : RowSquare [7,6,4,3,2,2,2,2,2,2,1] [6,6,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg12650

lemma sg21114 : RowSquare [7,6,4,3,2,2,2,2,2,2,1] [6,6,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg12651

lemma sg21115 : RowSquare [7,6,4,3,2,2,2,2,2,2,1] [6,6,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg12652

lemma sg21116 : RowSquare [7,6,4,3,2,2,2,2,2,2,1] [6,6,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg367 sg12653

lemma sg21117 : RowSquare [7,6,4,4,3,2,1,1,1,1,1,1,1] [6,6,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg3702 sg5301

lemma sg21118 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg403 sg12671

lemma sg21119 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg403 sg12673

lemma sg21120 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg403 sg12674

lemma sg21121 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [5,5,5,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg647 sg11799

lemma sg21122 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [5,5,5,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg647 sg11800

lemma sg21123 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg648 sg11795

lemma sg21124 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [6,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg648 sg11796

lemma sg21125 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg12672

lemma sg21126 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg651 sg11795

lemma sg21127 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg408 sg12669

lemma sg21128 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg408 sg12670

lemma sg21129 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg648 sg11803

lemma sg21130 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,3,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg651 sg11798

lemma sg21131 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg648 sg11804

lemma sg21132 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg12675

lemma sg21133 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg402 sg12678

lemma sg21134 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg12676

lemma sg21135 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [7,7,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg12677

lemma sg21136 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [8,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg411 sg12669

lemma sg21137 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [8,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg412 sg12669

lemma sg21138 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [8,4,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg412 sg12670

lemma sg21139 : RowSquare [7,7,3,2,2,2,2,2,2,2,1,1] [8,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg12678

lemma sg21140 : RowSquare [7,7,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2589 sg6503

lemma sg21141 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [5,4,4,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg12954

lemma sg21142 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [5,4,4,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg209 sg12955

lemma sg21143 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [5,4,4,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg209 sg12956

lemma sg21144 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg12952

lemma sg21145 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg12954

lemma sg21146 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg210 sg12955

lemma sg21147 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg210 sg12956

lemma sg21148 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg211 sg12950

lemma sg21149 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,3,3,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg211 sg12954

lemma sg21150 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,3,3,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg211 sg12955

lemma sg21151 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,3,3,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg211 sg12956

lemma sg21152 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,4,3,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg212 sg12954

lemma sg21153 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,4,3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg212 sg12955

lemma sg21154 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,4,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg212 sg12956

lemma sg21155 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg12952

lemma sg21156 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg12954

lemma sg21157 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg213 sg12955

lemma sg21158 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg213 sg12956

lemma sg21159 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg12950

lemma sg21160 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg12951

lemma sg21161 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg12954

lemma sg21162 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg214 sg12955

lemma sg21163 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg214 sg12956

lemma sg21164 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg12950

lemma sg21165 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg12954

lemma sg21166 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg215 sg12955

lemma sg21167 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg215 sg12956

lemma sg21168 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg12948

lemma sg21169 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg12949

lemma sg21170 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg12950

lemma sg21171 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg12951

lemma sg21172 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg12957

lemma sg21173 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg12958

lemma sg21174 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg12959

lemma sg21175 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg12957

lemma sg21176 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg12958

lemma sg21177 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg12959

lemma sg21178 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg12969

lemma sg21179 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [8,8,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg12970

lemma sg21180 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [9,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg217 sg12948

lemma sg21181 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [9,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg217 sg12949

lemma sg21182 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [9,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg217 sg12950

lemma sg21183 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [9,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg217 sg12951

lemma sg21184 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [9,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg12957

lemma sg21185 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [9,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg12958

lemma sg21186 : RowSquare [8,7,2,2,2,2,2,2,2,2,1,1] [9,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg12959

lemma sg21187 : RowSquare [8,7,3,3,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg6488

lemma sg21188 : RowSquare [8,7,3,3,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg6489

lemma sg21189 : RowSquare [8,7,3,3,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg14533

lemma sg21190 : RowSquare [8,7,3,3,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg14534

lemma sg21191 : RowSquare [8,7,3,3,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg14535

lemma sg21192 : RowSquare [8,7,3,3,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg80 sg14536

lemma sg21193 : RowSquare [8,7,3,3,3,2,1,1,1,1,1,1,1] [6,5,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2588 sg6488

lemma sg21194 : RowSquare [8,7,3,3,3,2,1,1,1,1,1,1,1] [6,6,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg2589 sg6488

lemma sg21195 : RowSquare [8,8,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg15262

lemma sg21196 : RowSquare [8,8,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg15263

lemma sg21197 : RowSquare [8,8,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg15264

lemma sg21198 : RowSquare [8,8,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19 sg15265

lemma sg21199 : RowSquare [9,7,3,3,2,2,1,1,1,1,1,1,1] [5,5,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4165 sg4842

lemma sg21200 : RowSquare [9,7,3,3,2,2,1,1,1,1,1,1,1] [6,6,6,6,5,4] := by
  exact rowSquare_join (by decide) sg4173 sg4842

lemma sg21201 : RowSquare [9,7,3,3,2,2,1,1,1,1,1,1,1] [6,6,6,6,6,3] := by
  exact rowSquare_join (by decide) sg4174 sg4842

lemma sg21202 : RowSquare [9,8,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3264 sg5760

lemma sg21203 : RowSquare [9,9,3,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3927 sg4821

lemma sg21204 : RowSquare [9,9,3,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3927 sg4820

lemma sg21205 : RowSquare [9,9,3,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3927 sg4819

lemma sg21206 : RowSquare [9,9,3,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3927 sg4818

lemma sg21207 : RowSquare [9,9,3,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3927 sg4817

lemma sg21208 : RowSquare [9,9,3,2,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3927 sg4814

lemma sg21209 : RowSquare [10,9,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3839 sg4932

lemma sg21210 : RowSquare [7,6,4,3,2,2,2,2,2,2,1,1] [5,5,5,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg12650

lemma sg21211 : RowSquare [7,6,4,3,2,2,2,2,2,2,1,1] [5,5,5,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg12651

lemma sg21212 : RowSquare [7,6,4,3,2,2,2,2,2,2,1,1] [5,5,5,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg12652

lemma sg21213 : RowSquare [7,6,4,3,2,2,2,2,2,2,1,1] [5,5,5,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg658 sg12653

lemma sg21214 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg14529

lemma sg21215 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg14530

lemma sg21216 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg14531

lemma sg21217 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg210 sg14532

lemma sg21218 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg361 sg12952

lemma sg21219 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg361 sg12954

lemma sg21220 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg361 sg12955

lemma sg21221 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg361 sg12956

lemma sg21222 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [5,5,5,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg357 sg12965

lemma sg21223 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,3,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg362 sg12956

lemma sg21224 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg14530

lemma sg21225 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg14531

lemma sg21226 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg213 sg14532

lemma sg21227 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12952

lemma sg21228 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12953

lemma sg21229 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12954

lemma sg21230 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12955

lemma sg21231 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg363 sg12956

lemma sg21232 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,6,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg356 sg12967

lemma sg21233 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [6,6,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg356 sg12968

lemma sg21234 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg14527

lemma sg21235 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg14530

lemma sg21236 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg14531

lemma sg21237 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg214 sg14532

lemma sg21238 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg14530

lemma sg21239 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg14531

lemma sg21240 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg215 sg14532

lemma sg21241 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12960

lemma sg21242 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg360 sg12966

lemma sg21243 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12961

lemma sg21244 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12962

lemma sg21245 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,7,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12963

lemma sg21246 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [7,7,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12964

lemma sg21247 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [8,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg14527

lemma sg21248 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [8,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg14528

lemma sg21249 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [8,3,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg216 sg14532

lemma sg21250 : RowSquare [8,7,3,2,2,2,2,2,2,2,1,1] [8,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg12966

lemma sg21251 : RowSquare [8,7,3,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4165 sg5738

lemma sg21252 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [5,5,5,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg97 sg14795

lemma sg21253 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg100 sg14791

lemma sg21254 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg100 sg14792

lemma sg21255 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg100 sg14793

lemma sg21256 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg100 sg14794

lemma sg21257 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg14791

lemma sg21258 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg14792

lemma sg21259 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg101 sg14793

lemma sg21260 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg101 sg14794

lemma sg21261 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg102 sg14791

lemma sg21262 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg102 sg14792

lemma sg21263 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg102 sg14793

lemma sg21264 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg102 sg14794

lemma sg21265 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg14788

lemma sg21266 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg14789

lemma sg21267 : RowSquare [8,8,2,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg14790

lemma sg21268 : RowSquare [8,8,3,3,3,2,1,1,1,1,1,1,1] [6,6,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg3263 sg6488

lemma sg21269 : RowSquare [8,8,3,3,3,2,1,1,1,1,1,1,1] [6,6,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg3264 sg6488

lemma sg21270 : RowSquare [9,8,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4025 sg5760

lemma sg21271 : RowSquare [9,8,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4026 sg5760

lemma sg21272 : RowSquare [9,8,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4029 sg5760

lemma sg21273 : RowSquare [9,8,3,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg20772

lemma sg21274 : RowSquare [9,8,3,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg20773

lemma sg21275 : RowSquare [9,8,3,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg20774

lemma sg21276 : RowSquare [9,8,3,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg20775

lemma sg21277 : RowSquare [9,8,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg15685

lemma sg21278 : RowSquare [9,8,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg15686

lemma sg21279 : RowSquare [9,8,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg15687

lemma sg21280 : RowSquare [9,8,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg12 sg15688

lemma sg21281 : RowSquare [9,8,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg12 sg15689

lemma sg21282 : RowSquare [10,9,2,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg4775

lemma sg21283 : RowSquare [10,9,2,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg4774

lemma sg21284 : RowSquare [10,9,2,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg4773

lemma sg21285 : RowSquare [10,9,2,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg4772

lemma sg21286 : RowSquare [10,9,2,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg4771

lemma sg21287 : RowSquare [10,9,2,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg4770

lemma sg21288 : RowSquare [10,9,2,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3982 sg5600

lemma sg21289 : RowSquare [7,7,4,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg14493

lemma sg21290 : RowSquare [7,7,4,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg14494

lemma sg21291 : RowSquare [7,7,4,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg14495

lemma sg21292 : RowSquare [7,7,4,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg14496

lemma sg21293 : RowSquare [7,7,4,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg407 sg14497

lemma sg21294 : RowSquare [8,7,3,3,2,2,2,2,2,2,1,1] [6,3,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg362 sg14529

lemma sg21295 : RowSquare [8,7,3,3,2,2,2,2,2,2,1,1] [6,6,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg356 sg14537

lemma sg21296 : RowSquare [8,7,3,3,2,2,2,2,2,2,1,1] [6,6,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg356 sg14538

lemma sg21297 : RowSquare [8,7,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg4173 sg6488

lemma sg21298 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg199 sg14790

lemma sg21299 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg199 sg14791

lemma sg21300 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg199 sg14792

lemma sg21301 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg199 sg14793

lemma sg21302 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg199 sg14794

lemma sg21303 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg100 sg15262

lemma sg21304 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg100 sg15263

lemma sg21305 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg100 sg15264

lemma sg21306 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg100 sg15265

lemma sg21307 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg15262

lemma sg21308 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg15263

lemma sg21309 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg15264

lemma sg21310 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg101 sg15265

lemma sg21311 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg202 sg14790

lemma sg21312 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg202 sg14791

lemma sg21313 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg202 sg14792

lemma sg21314 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg202 sg14793

lemma sg21315 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg202 sg14794

lemma sg21316 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,5,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg14798

lemma sg21317 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [6,5,5,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg193 sg14799

lemma sg21318 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg102 sg15262

lemma sg21319 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg102 sg15263

lemma sg21320 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg102 sg15264

lemma sg21321 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg102 sg15265

lemma sg21322 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,5,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg4852 sg5732

lemma sg21323 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,5,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg3281 sg7993

lemma sg21324 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,5,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg3994 sg6485

lemma sg21325 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,5,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg14800

lemma sg21326 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,5,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg193 sg14801

lemma sg21327 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [7,5,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg3275 sg7994

lemma sg21328 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg15260

lemma sg21329 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg15261

lemma sg21330 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg15262

lemma sg21331 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg15263

lemma sg21332 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg15264

lemma sg21333 : RowSquare [8,8,3,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg103 sg15265

lemma sg21334 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg15685

lemma sg21335 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg15686

lemma sg21336 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg15687

lemma sg21337 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg43 sg15688

lemma sg21338 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg43 sg15689

lemma sg21339 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg15684

end UniversalTensorSquare
end
end

end OAI
