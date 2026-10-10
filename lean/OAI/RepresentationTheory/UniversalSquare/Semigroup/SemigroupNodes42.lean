import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes36

namespace OAI

/-! Semigroup Nodes 42. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17340 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13749

lemma sg17341 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13750

lemma sg17342 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg3556 sg4310

lemma sg17343 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13751

lemma sg17344 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13752

lemma sg17345 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13753

lemma sg17346 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13754

lemma sg17347 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,4] := by
  exact rowSquare_join (by decide) sg13 sg13755

lemma sg17348 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13756

lemma sg17349 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13757

lemma sg17350 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg13 sg13758

lemma sg17351 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14866

lemma sg17352 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14867

lemma sg17353 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg14868

lemma sg17354 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14869

lemma sg17355 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3579 sg4192

lemma sg17356 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13759

lemma sg17357 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14870

lemma sg17358 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14871

lemma sg17359 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg3325 sg4476

lemma sg17360 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14872

lemma sg17361 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14873

lemma sg17362 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3403 sg4391

lemma sg17363 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14874

lemma sg17364 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg14875

lemma sg17365 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14876

lemma sg17366 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14877

lemma sg17367 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg14878

lemma sg17368 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14879

lemma sg17369 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14880

lemma sg17370 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13760

lemma sg17371 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13761

lemma sg17372 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14881

lemma sg17373 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14882

lemma sg17374 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14883

lemma sg17375 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14884

lemma sg17376 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg3403 sg4392

lemma sg17377 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14885

lemma sg17378 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1 sg14886

lemma sg17379 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14887

lemma sg17380 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14888

lemma sg17381 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14889

lemma sg17382 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg14890

lemma sg17383 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13762

lemma sg17384 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13763

lemma sg17385 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14891

lemma sg17386 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13764

lemma sg17387 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13765

lemma sg17388 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14892

lemma sg17389 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14893

lemma sg17390 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14894

lemma sg17391 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg14895

lemma sg17392 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1 sg14896

lemma sg17393 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13766

lemma sg17394 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13767

lemma sg17395 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13768

lemma sg17396 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13769

lemma sg17397 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13770

lemma sg17398 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13771

lemma sg17399 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13772

lemma sg17400 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13773

lemma sg17401 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13774

lemma sg17402 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13775

lemma sg17403 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg13 sg13776

lemma sg17404 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14898

lemma sg17405 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14899

lemma sg17406 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1 sg14900

lemma sg17407 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14901

lemma sg17408 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3587 sg4192

lemma sg17409 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg14902

lemma sg17410 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14903

lemma sg17411 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14904

lemma sg17412 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13672

lemma sg17413 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13673

lemma sg17414 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13777

lemma sg17415 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13778

lemma sg17416 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14905

lemma sg17417 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13779

lemma sg17418 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13780

lemma sg17419 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14906

lemma sg17420 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13676

lemma sg17421 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13677

lemma sg17422 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13678

lemma sg17423 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg14 sg13679

lemma sg17424 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14907

lemma sg17425 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14908

lemma sg17426 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14909

lemma sg17427 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14910

lemma sg17428 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14911

lemma sg17429 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg14912

lemma sg17430 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13781

lemma sg17431 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13782

lemma sg17432 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13783

lemma sg17433 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13784

lemma sg17434 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13785

lemma sg17435 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13786

lemma sg17436 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14913

lemma sg17437 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14914

lemma sg17438 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14915

lemma sg17439 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg14916

lemma sg17440 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg14917

lemma sg17441 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13787

lemma sg17442 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13788

lemma sg17443 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13789

lemma sg17444 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13790

lemma sg17445 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13791

lemma sg17446 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13792

lemma sg17447 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13793

lemma sg17448 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13794

lemma sg17449 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13795

lemma sg17450 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14918

lemma sg17451 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1 sg14919

lemma sg17452 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13796

lemma sg17453 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13797

lemma sg17454 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14920

lemma sg17455 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14921

lemma sg17456 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14922

lemma sg17457 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg14923

lemma sg17458 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13798

lemma sg17459 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13799

lemma sg17460 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13800

lemma sg17461 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13801

lemma sg17462 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13802

lemma sg17463 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13803

lemma sg17464 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14924

lemma sg17465 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14925

lemma sg17466 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg14926

lemma sg17467 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13804

lemma sg17468 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13805

lemma sg17469 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13806

lemma sg17470 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13807

lemma sg17471 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13808

lemma sg17472 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13809

lemma sg17473 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13810

lemma sg17474 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,2] := by
  exact rowSquare_join (by decide) sg13 sg13811

lemma sg17475 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg1 sg14927

lemma sg17476 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13812

lemma sg17477 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13813

lemma sg17478 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13814

lemma sg17479 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13815

lemma sg17480 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13816

lemma sg17481 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13817

lemma sg17482 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg13818

lemma sg17483 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3573 sg4201

lemma sg17484 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4477

lemma sg17485 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13680

lemma sg17486 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13681

lemma sg17487 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3574 sg4201

lemma sg17488 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3552 sg4313

lemma sg17489 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13682

lemma sg17490 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4478

lemma sg17491 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13683

lemma sg17492 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13684

lemma sg17493 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13819

lemma sg17494 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13820

lemma sg17495 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13821

lemma sg17496 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13822

lemma sg17497 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13823

lemma sg17498 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13824

lemma sg17499 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3552 sg4314

lemma sg17500 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13686

lemma sg17501 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13687

lemma sg17502 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13688

lemma sg17503 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg14 sg13689

lemma sg17504 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13825

lemma sg17505 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13826

lemma sg17506 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4479

lemma sg17507 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13691

lemma sg17508 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13692

lemma sg17509 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13693

lemma sg17510 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13827

lemma sg17511 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13828

lemma sg17512 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13829

lemma sg17513 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13830

lemma sg17514 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13831

lemma sg17515 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13832

lemma sg17516 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13698

lemma sg17517 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13699

lemma sg17518 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg13700

lemma sg17519 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13833

lemma sg17520 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13834

lemma sg17521 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13835

lemma sg17522 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13836

lemma sg17523 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13837

lemma sg17524 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13838

lemma sg17525 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13839

lemma sg17526 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg13 sg13840

lemma sg17527 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,5,1] := by
  exact rowSquare_join (by decide) sg14 sg13708

lemma sg17528 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3574 sg4202

lemma sg17529 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3673 sg4113

lemma sg17530 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13841

lemma sg17531 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13842

lemma sg17532 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3552 sg4315

lemma sg17533 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3402 sg4393

lemma sg17534 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3403 sg4393

lemma sg17535 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3329 sg4473

lemma sg17536 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13843

lemma sg17537 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13844

lemma sg17538 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13845

lemma sg17539 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13846

lemma sg17540 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13847

lemma sg17541 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13848

lemma sg17542 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3576 sg4203

lemma sg17543 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg3332 sg4472

lemma sg17544 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13849

lemma sg17545 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13850

lemma sg17546 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13851

lemma sg17547 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13852

lemma sg17548 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13853

lemma sg17549 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13854

lemma sg17550 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,5] := by
  exact rowSquare_join (by decide) sg3556 sg4312

lemma sg17551 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13855

lemma sg17552 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13856

lemma sg17553 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13857

lemma sg17554 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13858

lemma sg17555 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg13 sg13859

lemma sg17556 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,7,5,4] := by
  exact rowSquare_join (by decide) sg83 sg12343

lemma sg17557 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,7,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13861

lemma sg17558 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,7,6,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13862

lemma sg17559 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,7,6,3] := by
  exact rowSquare_join (by decide) sg13 sg13863

lemma sg17560 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,7,7,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13864

lemma sg17561 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,7,7,2] := by
  exact rowSquare_join (by decide) sg13 sg13865

lemma sg17562 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3671 sg4116

lemma sg17563 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3335 sg4465

lemma sg17564 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13866

lemma sg17565 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3573 sg4204

lemma sg17566 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3587 sg4195

lemma sg17567 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13709

lemma sg17568 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4480

lemma sg17569 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13710

lemma sg17570 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13711

lemma sg17571 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4205

lemma sg17572 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13867

lemma sg17573 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4481

lemma sg17574 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13713

lemma sg17575 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13714

lemma sg17576 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13715

lemma sg17577 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13868

lemma sg17578 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4206

lemma sg17579 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13869

lemma sg17580 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4207

lemma sg17581 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13870

lemma sg17582 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13871

lemma sg17583 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13872

lemma sg17584 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13720

lemma sg17585 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13721

lemma sg17586 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg13722

lemma sg17587 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3574 sg4205

lemma sg17588 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13723

lemma sg17589 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4482

lemma sg17590 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13873

lemma sg17591 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3574 sg4207

lemma sg17592 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13724

lemma sg17593 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13725

lemma sg17594 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13726

lemma sg17595 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4208

lemma sg17596 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13874

lemma sg17597 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13875

lemma sg17598 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13876

lemma sg17599 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13877

lemma sg17600 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13878

lemma sg17601 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13732

lemma sg17602 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,4,2] := by
  exact rowSquare_join (by decide) sg14 sg13733

lemma sg17603 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4209

lemma sg17604 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13879

lemma sg17605 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13880

lemma sg17606 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13881

lemma sg17607 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13882

lemma sg17608 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13883

lemma sg17609 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,5] := by
  exact rowSquare_join (by decide) sg14 sg13739

lemma sg17610 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4483

lemma sg17611 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg55 sg12475

lemma sg17612 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4210

lemma sg17613 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12476

lemma sg17614 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg55 sg12477

lemma sg17615 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12478

lemma sg17616 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13744

lemma sg17617 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13745

lemma sg17618 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3573 sg4211

lemma sg17619 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13884

lemma sg17620 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg55 sg12479

lemma sg17621 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12480

lemma sg17622 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13885

lemma sg17623 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,4,1] := by
  exact rowSquare_join (by decide) sg83 sg12344

lemma sg17624 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13886

lemma sg17625 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13887

lemma sg17626 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13888

lemma sg17627 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13889

lemma sg17628 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,4] := by
  exact rowSquare_join (by decide) sg13 sg13890

lemma sg17629 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13891

lemma sg17630 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13892

lemma sg17631 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,3] := by
  exact rowSquare_join (by decide) sg13 sg13893

lemma sg17632 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,7,4,4] := by
  exact rowSquare_join (by decide) sg83 sg12346

lemma sg17633 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,7,5,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13894

lemma sg17634 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,7,5,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12347

lemma sg17635 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,7,5,3] := by
  exact rowSquare_join (by decide) sg83 sg12348

lemma sg17636 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,7,6,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13895

lemma sg17637 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,7,6,2] := by
  exact rowSquare_join (by decide) sg13 sg13896

lemma sg17638 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,7,7,1] := by
  exact rowSquare_join (by decide) sg13 sg13897

lemma sg17639 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,3,2,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12487

lemma sg17640 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,3,2,2] := by
  exact rowSquare_join (by decide) sg55 sg12488

lemma sg17641 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,3,3,1] := by
  exact rowSquare_join (by decide) sg83 sg12349

lemma sg17642 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,4,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12489

lemma sg17643 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,4,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12350

lemma sg17644 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,4,3] := by
  exact rowSquare_join (by decide) sg83 sg12351

lemma sg17645 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,5,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12352

lemma sg17646 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,5,2] := by
  exact rowSquare_join (by decide) sg83 sg12353

lemma sg17647 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,6,1] := by
  exact rowSquare_join (by decide) sg83 sg12354

lemma sg17648 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,8,7] := by
  exact rowSquare_join (by decide) sg13 sg13898

lemma sg17649 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14928

lemma sg17650 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14929

lemma sg17651 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg14930

lemma sg17652 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14931

lemma sg17653 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14932

lemma sg17654 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg14933

lemma sg17655 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8 sg14121

lemma sg17656 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13899

lemma sg17657 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13900

lemma sg17658 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13901

lemma sg17659 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14934

lemma sg17660 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg13652

lemma sg17661 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14935

lemma sg17662 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg15 sg13653

lemma sg17663 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg3403 sg4394

lemma sg17664 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14936

lemma sg17665 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg15 sg13654

lemma sg17666 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14937

lemma sg17667 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14938

lemma sg17668 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13759

lemma sg17669 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8 sg14122

lemma sg17670 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14939

lemma sg17671 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14940

lemma sg17672 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg14941

lemma sg17673 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13902

lemma sg17674 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13903

lemma sg17675 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13904

lemma sg17676 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13905

lemma sg17677 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13906

lemma sg17678 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14942

lemma sg17679 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg15 sg13655

lemma sg17680 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg15 sg13656

lemma sg17681 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg15 sg13657

lemma sg17682 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg15 sg13658

lemma sg17683 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8 sg14123

lemma sg17684 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14943

lemma sg17685 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg13659

lemma sg17686 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14944

lemma sg17687 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg15 sg13660

lemma sg17688 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg15 sg13661

lemma sg17689 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13907

lemma sg17690 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13908

lemma sg17691 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13909

lemma sg17692 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13910

lemma sg17693 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13911

lemma sg17694 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13912

lemma sg17695 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14945

lemma sg17696 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg15 sg13663

lemma sg17697 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg15 sg13664

lemma sg17698 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg15 sg13665

lemma sg17699 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg14946

lemma sg17700 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13913

lemma sg17701 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13914

lemma sg17702 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13915

lemma sg17703 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13916

lemma sg17704 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13917

lemma sg17705 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13918

lemma sg17706 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13919

lemma sg17707 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13920

lemma sg17708 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13921

lemma sg17709 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg15 sg13671

lemma sg17710 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1 sg14947

lemma sg17711 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14948

lemma sg17712 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14949

lemma sg17713 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13760

lemma sg17714 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13761

lemma sg17715 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14950

lemma sg17716 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13762

lemma sg17717 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13763

lemma sg17718 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14951

lemma sg17719 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13764

lemma sg17720 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13765

lemma sg17721 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13922

lemma sg17722 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13923

lemma sg17723 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13924

lemma sg17724 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13925

lemma sg17725 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13926

lemma sg17726 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13927

lemma sg17727 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13772

lemma sg17728 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13773

lemma sg17729 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13774

lemma sg17730 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13775

lemma sg17731 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg14 sg13776

lemma sg17732 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13928

lemma sg17733 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13929

lemma sg17734 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14952

lemma sg17735 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14953

lemma sg17736 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14954

lemma sg17737 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg14955

lemma sg17738 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13930

lemma sg17739 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13931

end UniversalTensorSquare
end
end

end OAI
