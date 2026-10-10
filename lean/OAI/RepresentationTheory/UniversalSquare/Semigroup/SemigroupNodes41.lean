import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes29
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes30
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes35
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes33

namespace OAI

/-! Semigroup Nodes 41. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16940 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg74 sg12403

lemma sg16941 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg74 sg12404

lemma sg16942 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12405

lemma sg16943 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12406

lemma sg16944 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12407

lemma sg16945 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12358

lemma sg16946 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg142 sg11555

lemma sg16947 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg13812

lemma sg16948 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12408

lemma sg16949 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12360

lemma sg16950 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg142 sg11556

lemma sg16951 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg142 sg11557

lemma sg16952 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,5] := by
  exact rowSquare_join (by decide) sg75 sg12363

lemma sg16953 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12442

lemma sg16954 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg142 sg11558

lemma sg16955 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg142 sg11559

lemma sg16956 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,4] := by
  exact rowSquare_join (by decide) sg75 sg12365

lemma sg16957 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg10 sg13780

lemma sg16958 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg22 sg12821

lemma sg16959 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12797

lemma sg16960 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg26 sg12798

lemma sg16961 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12409

lemma sg16962 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg74 sg12410

lemma sg16963 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg27 sg12794

lemma sg16964 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12411

lemma sg16965 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12799

lemma sg16966 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12412

lemma sg16967 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12413

lemma sg16968 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12366

lemma sg16969 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg142 sg11560

lemma sg16970 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13812

lemma sg16971 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12414

lemma sg16972 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12443

lemma sg16973 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg142 sg11561

lemma sg16974 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg142 sg11562

lemma sg16975 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,5] := by
  exact rowSquare_join (by decide) sg75 sg12370

lemma sg16976 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12415

lemma sg16977 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12416

lemma sg16978 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg13849

lemma sg16979 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12417

lemma sg16980 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12371

lemma sg16981 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg142 sg11563

lemma sg16982 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg142 sg11564

lemma sg16983 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12374

lemma sg16984 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg142 sg11565

lemma sg16985 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,3,1] := by
  exact rowSquare_join (by decide) sg142 sg11566

lemma sg16986 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,4] := by
  exact rowSquare_join (by decide) sg143 sg11557

lemma sg16987 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12444

lemma sg16988 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,2,1] := by
  exact rowSquare_join (by decide) sg142 sg11567

lemma sg16989 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,3] := by
  exact rowSquare_join (by decide) sg143 sg11559

lemma sg16990 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg23 sg12821

lemma sg16991 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12418

lemma sg16992 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12419

lemma sg16993 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12420

lemma sg16994 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg29 sg12786

lemma sg16995 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg142 sg11569

lemma sg16996 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12421

lemma sg16997 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12422

lemma sg16998 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13849

lemma sg16999 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12423

lemma sg17000 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12380

lemma sg17001 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,3,2] := by
  exact rowSquare_join (by decide) sg142 sg11570

lemma sg17002 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,4,1] := by
  exact rowSquare_join (by decide) sg142 sg11571

lemma sg17003 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12800

lemma sg17004 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,2] := by
  exact rowSquare_join (by decide) sg142 sg11572

lemma sg17005 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,3,1] := by
  exact rowSquare_join (by decide) sg142 sg11573

lemma sg17006 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,4] := by
  exact rowSquare_join (by decide) sg143 sg11562

lemma sg17007 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13860

lemma sg17008 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg123 sg11595

lemma sg17009 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12385

lemma sg17010 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,3,3,2] := by
  exact rowSquare_join (by decide) sg142 sg11574

lemma sg17011 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg123 sg11596

lemma sg17012 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,2] := by
  exact rowSquare_join (by decide) sg142 sg11575

lemma sg17013 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,3,1] := by
  exact rowSquare_join (by decide) sg142 sg11576

lemma sg17014 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,4] := by
  exact rowSquare_join (by decide) sg143 sg11564

lemma sg17015 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg123 sg11597

lemma sg17016 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,5,2,1] := by
  exact rowSquare_join (by decide) sg142 sg11577

lemma sg17017 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,5,3] := by
  exact rowSquare_join (by decide) sg143 sg11566

lemma sg17018 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,6,1,1] := by
  exact rowSquare_join (by decide) sg142 sg11578

lemma sg17019 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,6,2] := by
  exact rowSquare_join (by decide) sg143 sg11567

lemma sg17020 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg10 sg13871

lemma sg17021 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg10 sg13872

lemma sg17022 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12424

lemma sg17023 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg12425

lemma sg17024 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4102

lemma sg17025 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12426

lemma sg17026 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13881

lemma sg17027 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,2] := by
  exact rowSquare_join (by decide) sg74 sg12427

lemma sg17028 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,4,1] := by
  exact rowSquare_join (by decide) sg143 sg11569

lemma sg17029 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg14668

lemma sg17030 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg14669

lemma sg17031 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg5 sg14643

lemma sg17032 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg14670

lemma sg17033 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg9 sg13899

lemma sg17034 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8 sg14082

lemma sg17035 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8 sg14083

lemma sg17036 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6 sg14641

lemma sg17037 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8 sg14084

lemma sg17038 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg12 sg13678

lemma sg17039 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg12 sg13679

lemma sg17040 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg14671

lemma sg17041 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13899

lemma sg17042 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg14672

lemma sg17043 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg9 sg13902

lemma sg17044 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg13904

lemma sg17045 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg9 sg13906

lemma sg17046 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg11 sg13766

lemma sg17047 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg11 sg13768

lemma sg17048 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg26 sg12801

lemma sg17049 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg11 sg13772

lemma sg17050 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg24 sg12820

lemma sg17051 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12428

lemma sg17052 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12429

lemma sg17053 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12802

lemma sg17054 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12430

lemma sg17055 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg74 sg12431

lemma sg17056 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12432

lemma sg17057 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12803

lemma sg17058 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12804

lemma sg17059 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12433

lemma sg17060 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12434

lemma sg17061 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg142 sg11579

lemma sg17062 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12805

lemma sg17063 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12806

lemma sg17064 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg12435

lemma sg17065 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg142 sg11580

lemma sg17066 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12445

lemma sg17067 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg142 sg11581

lemma sg17068 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg142 sg11582

lemma sg17069 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3 sg14674

lemma sg17070 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13902

lemma sg17071 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg13904

lemma sg17072 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg10 sg13906

lemma sg17073 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12807

lemma sg17074 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12436

lemma sg17075 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg27 sg12801

lemma sg17076 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12437

lemma sg17077 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12808

lemma sg17078 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12809

lemma sg17079 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg12438

lemma sg17080 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg27 sg12802

lemma sg17081 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12439

lemma sg17082 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg12803

lemma sg17083 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg27 sg12804

lemma sg17084 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12810

lemma sg17085 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12811

lemma sg17086 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12399

lemma sg17087 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12812

lemma sg17088 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12401

lemma sg17089 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,5,5] := by
  exact rowSquare_join (by decide) sg143 sg11582

lemma sg17090 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12440

lemma sg17091 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12813

lemma sg17092 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12446

lemma sg17093 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12814

lemma sg17094 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg123 sg11599

lemma sg17095 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg123 sg11600

lemma sg17096 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,5,4] := by
  exact rowSquare_join (by decide) sg145 sg11557

lemma sg17097 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12447

lemma sg17098 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,6,3] := by
  exact rowSquare_join (by decide) sg145 sg11559

lemma sg17099 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg27 sg12809

lemma sg17100 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12815

lemma sg17101 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg75 sg12409

lemma sg17102 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg29 sg12797

lemma sg17103 : RowSquare [6,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12448

lemma sg17104 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [4,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1461 sg7812

lemma sg17105 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [4,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1075 sg8780

lemma sg17106 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [4,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1464 sg7812

lemma sg17107 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1076 sg8780

lemma sg17108 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1461 sg7813

lemma sg17109 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg8780

lemma sg17110 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg7812

lemma sg17111 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1078 sg8780

lemma sg17112 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1469 sg7812

lemma sg17113 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [5,5,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1464 sg7815

lemma sg17114 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1470 sg7812

lemma sg17115 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1079 sg8780

lemma sg17116 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1471 sg7812

lemma sg17117 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1465 sg7813

lemma sg17118 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1080 sg8780

lemma sg17119 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1472 sg7812

lemma sg17120 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1467 sg7813

lemma sg17121 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1081 sg8780

lemma sg17122 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1082 sg8780

lemma sg17123 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg7813

lemma sg17124 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1473 sg7812

lemma sg17125 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg7814

lemma sg17126 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1078 sg8781

lemma sg17127 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg7815

lemma sg17128 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1474 sg7812

lemma sg17129 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1083 sg8780

lemma sg17130 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1475 sg7812

lemma sg17131 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1470 sg7813

lemma sg17132 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1084 sg8780

lemma sg17133 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1471 sg7813

lemma sg17134 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1085 sg8780

lemma sg17135 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1472 sg7813

lemma sg17136 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1086 sg8780

lemma sg17137 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1476 sg7812

lemma sg17138 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1468 sg7823

lemma sg17139 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [8,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1087 sg8780

lemma sg17140 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1477 sg7812

lemma sg17141 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1474 sg7813

lemma sg17142 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [8,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1088 sg8780

lemma sg17143 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [8,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1475 sg7813

lemma sg17144 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [8,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1089 sg8780

lemma sg17145 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [10,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1090 sg8780

lemma sg17146 : RowSquare [6,6,3,2,2,2,2,2,2,2,1,1] [11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1091 sg8780

lemma sg17147 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg6492

lemma sg17148 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4947

lemma sg17149 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg6494

lemma sg17150 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4949

lemma sg17151 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3325 sg4463

lemma sg17152 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2632 sg4945

lemma sg17153 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2630 sg4949

lemma sg17154 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2632 sg4947

lemma sg17155 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg2633 sg4947

lemma sg17156 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3353 sg4434

lemma sg17157 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2631 sg4949

lemma sg17158 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg4948

lemma sg17159 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg2632 sg4949

lemma sg17160 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg2633 sg4949

lemma sg17161 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2640 sg4942

lemma sg17162 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg3402 sg4376

lemma sg17163 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3402 sg4377

lemma sg17164 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3403 sg4377

lemma sg17165 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3401 sg4378

lemma sg17166 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2632 sg4951

lemma sg17167 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3325 sg4464

lemma sg17168 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13652

lemma sg17169 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13653

lemma sg17170 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3402 sg4378

lemma sg17171 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg13654

lemma sg17172 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3404 sg4374

lemma sg17173 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3552 sg4304

lemma sg17174 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg2635 sg4948

lemma sg17175 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg3402 sg4379

lemma sg17176 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg3403 sg4379

lemma sg17177 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg2636 sg4949

lemma sg17178 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2640 sg4943

lemma sg17179 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2632 sg4954

lemma sg17180 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2633 sg4954

lemma sg17181 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2632 sg4956

lemma sg17182 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2633 sg4956

lemma sg17183 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg4957

lemma sg17184 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13656

lemma sg17185 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13658

lemma sg17186 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3353 sg4435

lemma sg17187 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg3553 sg4304

lemma sg17188 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2633 sg4958

lemma sg17189 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg2639 sg4949

lemma sg17190 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg2640 sg4949

lemma sg17191 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13661

lemma sg17192 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3323 sg4468

lemma sg17193 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4468

lemma sg17194 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2632 sg4960

lemma sg17195 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,3,2] := by
  exact rowSquare_join (by decide) sg3554 sg4302

lemma sg17196 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13662

lemma sg17197 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2631 sg4962

lemma sg17198 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13663

lemma sg17199 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13664

lemma sg17200 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg3353 sg4436

lemma sg17201 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg3554 sg4304

lemma sg17202 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,3] := by
  exact rowSquare_join (by decide) sg2641 sg4949

lemma sg17203 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1675 sg6518

lemma sg17204 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1757 sg6495

lemma sg17205 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13666

lemma sg17206 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13667

lemma sg17207 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13668

lemma sg17208 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13669

lemma sg17209 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13670

lemma sg17210 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,3] := by
  exact rowSquare_join (by decide) sg3555 sg4303

lemma sg17211 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13671

lemma sg17212 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg3555 sg4304

lemma sg17213 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3556 sg4304

lemma sg17214 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2365 sg5734

lemma sg17215 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2272 sg5751

lemma sg17216 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg2273 sg5751

lemma sg17217 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2644 sg4942

lemma sg17218 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg3402 sg4380

lemma sg17219 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg3402 sg4381

lemma sg17220 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg3403 sg4381

lemma sg17221 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14865

lemma sg17222 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3402 sg4382

lemma sg17223 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3403 sg4382

lemma sg17224 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg3325 sg4469

lemma sg17225 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13672

lemma sg17226 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13673

lemma sg17227 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2635 sg4950

lemma sg17228 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg3325 sg4470

lemma sg17229 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg3403 sg4383

lemma sg17230 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3402 sg4384

lemma sg17231 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg3403 sg4384

lemma sg17232 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13674

lemma sg17233 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13675

lemma sg17234 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg3403 sg4385

lemma sg17235 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13676

lemma sg17236 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13677

lemma sg17237 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13678

lemma sg17238 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13679

lemma sg17239 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg3402 sg4386

lemma sg17240 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg3403 sg4386

lemma sg17241 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg3405 sg4379

lemma sg17242 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,4] := by
  exact rowSquare_join (by decide) sg2644 sg4949

lemma sg17243 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3402 sg4388

lemma sg17244 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg14 sg13654

lemma sg17245 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3406 sg4377

lemma sg17246 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg13 sg13689

lemma sg17247 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg3553 sg4307

lemma sg17248 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg3557 sg4304

lemma sg17249 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg3406 sg4379

lemma sg17250 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3582 sg4190

lemma sg17251 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg3325 sg4473

lemma sg17252 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3403 sg4389

lemma sg17253 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13690

lemma sg17254 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13691

lemma sg17255 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13692

lemma sg17256 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13693

lemma sg17257 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg3402 sg4390

lemma sg17258 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg3403 sg4390

lemma sg17259 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg3576 sg4193

lemma sg17260 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13694

lemma sg17261 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13695

lemma sg17262 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13696

lemma sg17263 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13697

lemma sg17264 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13698

lemma sg17265 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13699

lemma sg17266 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13700

lemma sg17267 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg3576 sg4194

lemma sg17268 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,2] := by
  exact rowSquare_join (by decide) sg3675 sg4111

lemma sg17269 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3552 sg4311

lemma sg17270 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13701

lemma sg17271 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13702

lemma sg17272 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13703

lemma sg17273 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13704

lemma sg17274 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13705

lemma sg17275 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13706

lemma sg17276 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg13 sg13707

lemma sg17277 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg13 sg13708

lemma sg17278 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3556 sg4307

lemma sg17279 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13711

lemma sg17280 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13656

lemma sg17281 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13657

lemma sg17282 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg14 sg13658

lemma sg17283 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3404 sg4387

lemma sg17284 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,4] := by
  exact rowSquare_join (by decide) sg2640 sg4956

lemma sg17285 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2642 sg4953

lemma sg17286 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4196

lemma sg17287 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13717

lemma sg17288 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13718

lemma sg17289 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13719

lemma sg17290 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13720

lemma sg17291 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13721

lemma sg17292 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13722

lemma sg17293 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13671

lemma sg17294 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg3679 sg4111

lemma sg17295 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4474

lemma sg17296 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg3329 sg4467

lemma sg17297 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4475

lemma sg17298 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4199

lemma sg17299 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3553 sg4310

lemma sg17300 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg3329 sg4468

lemma sg17301 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,3] := by
  exact rowSquare_join (by decide) sg3332 sg4466

lemma sg17302 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4200

lemma sg17303 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13727

lemma sg17304 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13728

lemma sg17305 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13729

lemma sg17306 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13730

lemma sg17307 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13731

lemma sg17308 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13732

lemma sg17309 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg13 sg13733

lemma sg17310 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg3556 sg4309

lemma sg17311 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1675 sg6519

lemma sg17312 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13734

lemma sg17313 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13735

lemma sg17314 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13736

lemma sg17315 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13737

lemma sg17316 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13738

lemma sg17317 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg13739

lemma sg17318 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3354 sg4434

lemma sg17319 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3574 sg4197

lemma sg17320 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2889 sg4880

lemma sg17321 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3571 sg4212

lemma sg17322 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3574 sg4198

lemma sg17323 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13740

lemma sg17324 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3574 sg4199

lemma sg17325 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3593 sg4190

lemma sg17326 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3576 sg4197

lemma sg17327 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3332 sg4467

lemma sg17328 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3574 sg4200

lemma sg17329 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13741

lemma sg17330 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13742

lemma sg17331 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13743

lemma sg17332 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13744

lemma sg17333 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13745

lemma sg17334 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3576 sg4199

lemma sg17335 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg3332 sg4468

lemma sg17336 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1756 sg6496

lemma sg17337 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13746

lemma sg17338 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13747

lemma sg17339 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13748

end UniversalTensorSquare
end
end

end OAI
