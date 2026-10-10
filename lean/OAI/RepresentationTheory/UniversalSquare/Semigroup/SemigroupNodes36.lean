import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes29
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes30
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes22
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes35
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes33

namespace OAI

/-! Semigroup Nodes 36. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14940 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2913 sg3470

lemma sg14941 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2371 sg4322

lemma sg14942 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3491

lemma sg14943 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3492

lemma sg14944 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3110 sg3358

lemma sg14945 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3493

lemma sg14946 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg2752 sg3620

lemma sg14947 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2752 sg3622

lemma sg14948 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2741 sg3626

lemma sg14949 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2912 sg3472

lemma sg14950 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2905 sg3479

lemma sg14951 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2958 sg3413

lemma sg14952 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3494

lemma sg14953 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2904 sg3484

lemma sg14954 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3112 sg3358

lemma sg14955 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2743 sg3627

lemma sg14956 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2904 sg3485

lemma sg14957 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2743 sg3628

lemma sg14958 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg2746 sg3625

lemma sg14959 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg2915 sg3476

lemma sg14960 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2968 sg3409

lemma sg14961 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3495

lemma sg14962 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3113 sg3357

lemma sg14963 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2743 sg3629

lemma sg14964 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3113 sg3359

lemma sg14965 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5] := by
  exact rowSquare_join (by decide) sg3114 sg3359

lemma sg14966 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2744 sg3626

lemma sg14967 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2746 sg3626

lemma sg14968 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2958 sg3414

lemma sg14969 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg2746 sg3629

lemma sg14970 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2758 sg3614

lemma sg14971 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2902 sg3496

lemma sg14972 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3497

lemma sg14973 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2958 sg3416

lemma sg14974 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3498

lemma sg14975 : RowSquare [5,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3499

lemma sg14976 : RowSquare [5,5,3,3,2,2,2,2,2,2,1] [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg4833

lemma sg14977 : RowSquare [5,5,3,3,2,2,2,2,2,2,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1867 sg4832

lemma sg14978 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg3359

lemma sg14979 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1] [6,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg2144 sg4488

lemma sg14980 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2904 sg3359

lemma sg14981 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2743 sg3411

lemma sg14982 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg2144 sg4489

lemma sg14983 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1] [6,6,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg12441

lemma sg14984 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14009

lemma sg14985 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2752 sg3411

lemma sg14986 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2745 sg3560

lemma sg14987 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2743 sg3562

lemma sg14988 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2167 sg4443

lemma sg14989 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg1687 sg4993

lemma sg14990 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1688 sg4993

lemma sg14991 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg4994

lemma sg14992 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1687 sg4995

lemma sg14993 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1688 sg4995

lemma sg14994 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg1688 sg4996

lemma sg14995 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2743 sg3567

lemma sg14996 : RowSquare [5,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg2167 sg4446

lemma sg14997 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2605 sg3691

lemma sg14998 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2606 sg3691

lemma sg14999 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1688 sg4968

lemma sg15000 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,6,5] := by
  exact rowSquare_join (by decide) sg2962 sg3337

lemma sg15001 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14027

lemma sg15002 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2610 sg3691

lemma sg15003 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1] [6,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg4899

lemma sg15004 : RowSquare [6,4,3,2,2,2,2,2,2,2,1,1] [4,4,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1868 sg4862

lemma sg15005 : RowSquare [6,4,3,3,3,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1 sg14081

lemma sg15006 : RowSquare [6,4,3,3,3,2,1,1,1,1,1,1,1,1] [8,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg14679

lemma sg15007 : RowSquare [6,4,4,3,2,2,1,1,1,1,1,1,1,1] [10,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2 sg14028

lemma sg15008 : RowSquare [6,4,4,3,2,2,1,1,1,1,1,1,1,1] [10,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg9 sg12451

lemma sg15009 : RowSquare [6,4,4,3,2,2,1,1,1,1,1,1,1,1] [10,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2 sg14029

lemma sg15010 : RowSquare [6,4,4,3,2,2,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg12 sg12450

lemma sg15011 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [4,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1478 sg5672

lemma sg15012 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [5,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1480 sg5672

lemma sg15013 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [5,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1481 sg5672

lemma sg15014 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [5,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1482 sg5672

lemma sg15015 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1483 sg5672

lemma sg15016 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1485 sg5672

lemma sg15017 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1480 sg5673

lemma sg15018 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1487 sg5672

lemma sg15019 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1481 sg5673

lemma sg15020 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1482 sg5673

lemma sg15021 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,5,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1480 sg5674

lemma sg15022 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg5672

lemma sg15023 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [6,6,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1482 sg5674

lemma sg15024 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1489 sg5672

lemma sg15025 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1483 sg5673

lemma sg15026 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1490 sg5672

lemma sg15027 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1491 sg5672

lemma sg15028 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1484 sg5673

lemma sg15029 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1485 sg5673

lemma sg15030 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1492 sg5672

lemma sg15031 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1486 sg5673

lemma sg15032 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1487 sg5673

lemma sg15033 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1493 sg5672

lemma sg15034 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg5673

lemma sg15035 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [7,7,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg5674

lemma sg15036 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1494 sg5672

lemma sg15037 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1495 sg5672

lemma sg15038 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1489 sg5673

lemma sg15039 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1496 sg5672

lemma sg15040 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1490 sg5673

lemma sg15041 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1491 sg5673

lemma sg15042 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1497 sg5672

lemma sg15043 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1492 sg5673

lemma sg15044 : RowSquare [6,5,2,2,2,2,2,2,2,2,1,1] [8,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1493 sg5673

lemma sg15045 : RowSquare [6,5,3,2,2,2,2,2,2,2,1] [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1325 sg5672

lemma sg15046 : RowSquare [6,5,3,2,2,2,2,2,2,2,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg996 sg6457

lemma sg15047 : RowSquare [6,5,3,2,2,2,2,2,2,2,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1326 sg5672

lemma sg15048 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,4] := by
  exact rowSquare_join (by decide) sg1688 sg4949

lemma sg15049 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14087

lemma sg15050 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1] [7,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1 sg14088

lemma sg15051 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1] [8,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg5 sg12832

lemma sg15052 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1] [9,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg6 sg12832

lemma sg15053 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1] [9,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg15 sg12449

lemma sg15054 : RowSquare [6,5,3,3,2,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg991 sg6457

lemma sg15055 : RowSquare [6,5,3,3,2,2,2,2,2,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg6457

lemma sg15056 : RowSquare [6,5,3,3,2,2,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg994 sg6457

lemma sg15057 : RowSquare [6,5,3,3,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg6458

lemma sg15058 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1] [7,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg3415

lemma sg15059 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2720 sg3576

lemma sg15060 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2720 sg3578

lemma sg15061 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2272 sg4412

lemma sg15062 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg2273 sg4412

lemma sg15063 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1756 sg4981

lemma sg15064 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1756 sg4982

lemma sg15065 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2721 sg3576

lemma sg15066 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1758 sg4982

lemma sg15067 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2721 sg3578

lemma sg15068 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1756 sg4983

lemma sg15069 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1756 sg4984

lemma sg15070 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1758 sg4983

lemma sg15071 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1757 sg4984

lemma sg15072 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2722 sg3576

lemma sg15073 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1758 sg4984

lemma sg15074 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg2722 sg3578

lemma sg15075 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg2724 sg3576

lemma sg15076 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,2] := by
  exact rowSquare_join (by decide) sg2723 sg3578

lemma sg15077 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg2724 sg3578

lemma sg15078 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2726 sg3576

lemma sg15079 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg2726 sg3577

lemma sg15080 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg2726 sg3578

lemma sg15081 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2273 sg4413

lemma sg15082 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2722 sg3581

lemma sg15083 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1758 sg4985

lemma sg15084 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg2728 sg3578

lemma sg15085 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg2724 sg3581

lemma sg15086 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2729 sg3576

lemma sg15087 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2722 sg3584

lemma sg15088 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2730 sg3576

lemma sg15089 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg1762 sg4984

lemma sg15090 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg2891 sg3457

lemma sg15091 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg2891 sg3458

lemma sg15092 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2732 sg3576

lemma sg15093 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2722 sg3589

lemma sg15094 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2733 sg3576

lemma sg15095 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg2723 sg3589

lemma sg15096 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg2724 sg3589

lemma sg15097 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2891 sg3459

lemma sg15098 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg2891 sg3460

lemma sg15099 : RowSquare [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg2891 sg3461

lemma sg15100 : RowSquare [6,6,2,2,2,2,2,2,2,2,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg662 sg7812

lemma sg15101 : RowSquare [6,6,2,2,2,2,2,2,2,2,1] [5,5,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg658 sg7821

lemma sg15102 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg4949

lemma sg15103 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg1758 sg4948

lemma sg15104 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg1758 sg4949

lemma sg15105 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2273 sg4375

lemma sg15106 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2888 sg3403

lemma sg15107 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1759 sg4949

lemma sg15108 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg4376

lemma sg15109 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2632 sg3673

lemma sg15110 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2889 sg3403

lemma sg15111 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg3674

lemma sg15112 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1760 sg4948

lemma sg15113 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2632 sg3675

lemma sg15114 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2633 sg3675

lemma sg15115 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg1761 sg4947

lemma sg15116 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1758 sg4952

lemma sg15117 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg2273 sg4378

lemma sg15118 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2273 sg4379

lemma sg15119 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1762 sg4949

lemma sg15120 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2633 sg3676

lemma sg15121 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2633 sg3677

lemma sg15122 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg3678

lemma sg15123 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1763 sg4948

lemma sg15124 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2632 sg3679

lemma sg15125 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2633 sg3679

lemma sg15126 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1330 sg5769

lemma sg15127 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1756 sg4956

lemma sg15128 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2274 sg4377

lemma sg15129 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2274 sg4379

lemma sg15130 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1758 sg4955

lemma sg15131 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1758 sg4956

lemma sg15132 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1765 sg4949

lemma sg15133 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1758 sg4958

lemma sg15134 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1332 sg5770

lemma sg15135 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1766 sg4945

lemma sg15136 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg1766 sg4949

lemma sg15137 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2636 sg3675

lemma sg15138 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg2368 sg4303

lemma sg15139 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg2892 sg3404

lemma sg15140 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg2368 sg4304

lemma sg15141 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2636 sg3679

lemma sg15142 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg2640 sg3675

lemma sg15143 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2640 sg3679

lemma sg15144 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2896 sg3403

lemma sg15145 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg3682

lemma sg15146 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2635 sg3680

lemma sg15147 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2632 sg3683

lemma sg15148 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2633 sg3683

lemma sg15149 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2899 sg3403

lemma sg15150 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg3684

lemma sg15151 : RowSquare [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2636 sg3681

lemma sg15152 : RowSquare [6,6,3,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg648 sg7813

lemma sg15153 : RowSquare [6,6,3,2,2,2,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg651 sg7813

lemma sg15154 : RowSquare [6,6,3,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg8782

lemma sg15155 : RowSquare [6,6,3,2,2,2,2,2,2,1,1] [8,8,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg8783

lemma sg15156 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1] [6,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1618 sg4949

lemma sg15157 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1] [7,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg2644 sg3332

lemma sg15158 : RowSquare [7,5,3,3,3,2,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1682 sg4879

lemma sg15159 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2707 sg3579

lemma sg15160 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2707 sg3580

lemma sg15161 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg3584

lemma sg15162 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3576

lemma sg15163 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3577

lemma sg15164 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg3586

lemma sg15165 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg2260 sg4412

lemma sg15166 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3578

lemma sg15167 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2707 sg3587

lemma sg15168 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg3589

lemma sg15169 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg3592

lemma sg15170 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2725 sg3534

lemma sg15171 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2707 sg3594

lemma sg15172 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2720 sg3537

lemma sg15173 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2708 sg3594

lemma sg15174 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg3595

lemma sg15175 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2708 sg3595

lemma sg15176 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2707 sg3596

lemma sg15177 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2727 sg3534

lemma sg15178 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2710 sg3580

lemma sg15179 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2708 sg3597

lemma sg15180 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2881 sg3456

lemma sg15181 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2708 sg3598

lemma sg15182 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg3599

lemma sg15183 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2709 sg3581

lemma sg15184 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg3599

lemma sg15185 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3581

lemma sg15186 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2709 sg3582

lemma sg15187 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2708 sg3600

lemma sg15188 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg3601

lemma sg15189 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3583

lemma sg15190 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg3602

lemma sg15191 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3584

lemma sg15192 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3585

lemma sg15193 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2881 sg3458

lemma sg15194 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2707 sg3603

lemma sg15195 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2710 sg3587

lemma sg15196 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2708 sg3603

lemma sg15197 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2708 sg3604

lemma sg15198 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg3605

lemma sg15199 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3588

lemma sg15200 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2707 sg3606

lemma sg15201 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg3606

lemma sg15202 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3589

lemma sg15203 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg3607

lemma sg15204 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3590

lemma sg15205 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3591

lemma sg15206 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3593

lemma sg15207 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2256 sg4414

lemma sg15208 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2708 sg3608

lemma sg15209 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg3609

lemma sg15210 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3595

lemma sg15211 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3598

lemma sg15212 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3599

lemma sg15213 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3604

lemma sg15214 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3605

lemma sg15215 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3608

lemma sg15216 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3609

lemma sg15217 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3] := by
  exact rowSquare_join (by decide) sg227 sg11060

lemma sg15218 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg424 sg8893

lemma sg15219 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3] := by
  exact rowSquare_join (by decide) sg228 sg11060

lemma sg15220 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3610

lemma sg15221 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg3611

lemma sg15222 : RowSquare [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg3612

lemma sg15223 : RowSquare [7,6,2,2,2,2,2,2,2,1,1] [9,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg217 sg10869

lemma sg15224 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4377

lemma sg15225 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4378

lemma sg15226 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4388

lemma sg15227 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2366 sg4167

lemma sg15228 : RowSquare [7,6,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2367 sg4167

lemma sg15229 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1] [5,5,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg643 sg7995

lemma sg15230 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1] [6,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg643 sg7996

lemma sg15231 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1] [6,6,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg356 sg8893

lemma sg15232 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1] [7,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg643 sg7997

lemma sg15233 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1] [7,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg356 sg8894

lemma sg15234 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1] [8,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg645 sg7997

lemma sg15235 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2881 sg3316

lemma sg15236 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1 sg14446

lemma sg15237 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1 sg14447

lemma sg15238 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2156 sg4167

lemma sg15239 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg3294

lemma sg15240 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2710 sg3314

lemma sg15241 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg3317

lemma sg15242 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1] [7,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg74 sg11553

lemma sg15243 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1] [8,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg193 sg11058

lemma sg15244 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1] [9,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg391 sg8890

lemma sg15245 : RowSquare [7,7,3,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg12673

lemma sg15246 : RowSquare [7,7,3,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19 sg12674

lemma sg15247 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg5738

lemma sg15248 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg11549

lemma sg15249 : RowSquare [8,7,2,1,1,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2710 sg3522

lemma sg15250 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg3275

lemma sg15251 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg3260

lemma sg15252 : RowSquare [8,7,3,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2588 sg3522

lemma sg15253 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg3263

lemma sg15254 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2074 sg4348

lemma sg15255 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1] [5,4,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12597

lemma sg15256 : RowSquare [8,8,2,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2576 sg3522

lemma sg15257 : RowSquare [8,8,2,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2546 sg3522

lemma sg15258 : RowSquare [8,8,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12605

lemma sg15259 : RowSquare [8,8,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2529 sg3522

lemma sg15260 : RowSquare [8,8,3,2,2,2,2,2] [2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg3239

lemma sg15261 : RowSquare [8,8,3,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg3238

lemma sg15262 : RowSquare [8,8,3,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg3237

lemma sg15263 : RowSquare [8,8,3,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg3236

lemma sg15264 : RowSquare [8,8,3,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2566 sg3235

lemma sg15265 : RowSquare [8,8,3,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2566 sg3234

lemma sg15266 : RowSquare [8,8,3,2,2,2,2,2] [4,4,4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2562 sg3233

lemma sg15267 : RowSquare [9,7,2,2,2,1,1,1,1,1,1,1] [4,4,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg3258

lemma sg15268 : RowSquare [9,7,2,2,2,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg14783

lemma sg15269 : RowSquare [9,7,2,2,2,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2252 sg3966

lemma sg15270 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12615

lemma sg15271 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg11740

lemma sg15272 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg3953

lemma sg15273 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg11741

lemma sg15274 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg14784

lemma sg15275 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg75 sg11242

lemma sg15276 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg14786

lemma sg15277 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg9442

lemma sg15278 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg9444

lemma sg15279 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg451 sg7998

lemma sg15280 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg452 sg7998

lemma sg15281 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [9,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg453 sg7998

lemma sg15282 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1] [9,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg452 sg7999

lemma sg15283 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2699 sg3258

lemma sg15284 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2700 sg3258

lemma sg15285 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg11484

lemma sg15286 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg11485

lemma sg15287 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg168 sg10594

lemma sg15288 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg10595

lemma sg15289 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg165 sg10596

lemma sg15290 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg75 sg11485

lemma sg15291 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg11491

lemma sg15292 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg722 sg6502

lemma sg15293 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1] [9,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg430 sg8008

lemma sg15294 : RowSquare [12,3,2,2,2,2,2,2,1,1] [4,4,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg11484

lemma sg15295 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2925 sg4331

lemma sg15296 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg3634 sg3418

lemma sg15297 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg4335

lemma sg15298 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg3420

lemma sg15299 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg3724 sg3338

lemma sg15300 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2656 sg4501

lemma sg15301 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg1032 sg8003

lemma sg15302 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg1032 sg8004

lemma sg15303 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg1032 sg8005

lemma sg15304 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg1033 sg8005

lemma sg15305 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg3633 sg3421

lemma sg15306 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3633 sg3422

lemma sg15307 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg3635 sg3421

lemma sg15308 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3423

lemma sg15309 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3633 sg3424

lemma sg15310 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3421 sg3636

lemma sg15311 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg3701 sg3365

lemma sg15312 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3425

lemma sg15313 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3426

lemma sg15314 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3427

lemma sg15315 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg2930 sg4328

lemma sg15316 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg3638 sg3420

lemma sg15317 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg2930 sg4329

lemma sg15318 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3635 sg3422

lemma sg15319 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4521

lemma sg15320 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3428

lemma sg15321 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3635 sg3424

lemma sg15322 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3701 sg3367

lemma sg15323 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3636 sg3422

lemma sg15324 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4522

lemma sg15325 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3429

lemma sg15326 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3430

lemma sg15327 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg3360 sg3704

lemma sg15328 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4523

lemma sg15329 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3431

lemma sg15330 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3427

lemma sg15331 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg3704 sg3361

lemma sg15332 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg3704 sg3362

lemma sg15333 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3636 sg3424

lemma sg15334 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3432

lemma sg15335 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4524

lemma sg15336 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3433

lemma sg15337 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3640 sg3420

lemma sg15338 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg3360 sg3705

lemma sg15339 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4525

end UniversalTensorSquare
end
end

end OAI
