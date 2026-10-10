import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24

namespace OAI

/-! Semigroup Nodes 77. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31340 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9642

lemma sg31341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,5,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9590

lemma sg31342 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2208 sg15564

lemma sg31343 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2242 sg15536

lemma sg31344 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3170 sg14806

lemma sg31345 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3779 sg14543

lemma sg31346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5574 sg12630

lemma sg31347 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5264 sg12693

lemma sg31348 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8603 sg10088

lemma sg31349 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9297

lemma sg31350 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8666 sg9845

lemma sg31351 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3171 sg14806

lemma sg31352 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3780 sg14543

lemma sg31353 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5575 sg12630

lemma sg31354 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6600 sg11542

lemma sg31355 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10405

lemma sg31356 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9305

lemma sg31357 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8660 sg9848

lemma sg31358 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8742 sg9581

lemma sg31359 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5850 sg11840

lemma sg31360 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6601 sg11542

lemma sg31361 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8254 sg10849

lemma sg31362 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9385

lemma sg31363 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9856

lemma sg31364 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8817 sg9297

lemma sg31365 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8453 sg10317

lemma sg31366 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9300

lemma sg31367 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9980

lemma sg31368 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9591

lemma sg31369 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8818 sg9297

lemma sg31370 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9985

lemma sg31371 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9985

lemma sg31372 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3781 sg14543

lemma sg31373 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5851 sg11840

lemma sg31374 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6602 sg11542

lemma sg31375 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10502

lemma sg31376 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9385

lemma sg31377 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8660 sg9849

lemma sg31378 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10502

lemma sg31379 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6603 sg11542

lemma sg31380 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10409

lemma sg31381 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9386

lemma sg31382 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9980

lemma sg31383 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8817 sg9298

lemma sg31384 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9307

lemma sg31385 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9986

lemma sg31386 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9986

lemma sg31387 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9644

lemma sg31388 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8258 sg10849

lemma sg31389 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9387

lemma sg31390 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9987

lemma sg31391 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9987

lemma sg31392 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9982

lemma sg31393 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9645

lemma sg31394 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9592

lemma sg31395 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5852 sg11840

lemma sg31396 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6604 sg11542

lemma sg31397 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8259 sg10849

lemma sg31398 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9386

lemma sg31399 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8660 sg9852

lemma sg31400 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9298

lemma sg31401 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10410

lemma sg31402 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9388

lemma sg31403 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9988

lemma sg31404 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9988

lemma sg31405 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9983

lemma sg31406 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9646

lemma sg31407 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9389

lemma sg31408 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9984

lemma sg31409 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9647

lemma sg31410 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9645

lemma sg31411 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9862

lemma sg31412 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9593

lemma sg31413 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6605 sg11542

lemma sg31414 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8606 sg10087

lemma sg31415 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9388

lemma sg31416 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9989

lemma sg31417 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9989

lemma sg31418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9389

lemma sg31419 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9983

lemma sg31420 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9302

lemma sg31421 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9646

lemma sg31422 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9984

lemma sg31423 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9647

lemma sg31424 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,10,6,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9647

lemma sg31425 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,5,5,5,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10428

lemma sg31426 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,5,5,5,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9995

lemma sg31427 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,5,5,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8399 sg10611

lemma sg31428 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,5,5,5,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8382 sg10655

lemma sg31429 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,5,5,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8529 sg10156

lemma sg31430 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,5,5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10440

lemma sg31431 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,5,5,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9997

lemma sg31432 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,5,5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10441

lemma sg31433 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,5,5,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9998

lemma sg31434 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,5,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8434 sg10351

lemma sg31435 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,5,5,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9995

lemma sg31436 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,5,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9995

lemma sg31437 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8384 sg10655

lemma sg31438 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,5,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8531 sg10156

lemma sg31439 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10444

lemma sg31440 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9999

lemma sg31441 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10446

lemma sg31442 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10000

lemma sg31443 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9339

lemma sg31444 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9339

lemma sg31445 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9339

lemma sg31446 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10447

lemma sg31447 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10001

lemma sg31448 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9340

lemma sg31449 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9340

lemma sg31450 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9340

lemma sg31451 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9995

lemma sg31452 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9648

lemma sg31453 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8534 sg10156

lemma sg31454 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14521

lemma sg31455 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11349

lemma sg31456 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8827 sg9256

lemma sg31457 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9327

lemma sg31458 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10448

lemma sg31459 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10002

lemma sg31460 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10449

lemma sg31461 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10003

lemma sg31462 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9341

lemma sg31463 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9341

lemma sg31464 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9341

lemma sg31465 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8828 sg9258

lemma sg31466 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8872 sg9108

lemma sg31467 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9342

lemma sg31468 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9342

lemma sg31469 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9342

lemma sg31470 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9342

lemma sg31471 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8828 sg9259

lemma sg31472 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8872 sg9109

lemma sg31473 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9648

lemma sg31474 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8871 sg9110

lemma sg31475 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8828 sg9260

lemma sg31476 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,6,6,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8872 sg9110

lemma sg31477 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10458

lemma sg31478 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10004

lemma sg31479 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10460

lemma sg31480 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10005

lemma sg31481 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9349

lemma sg31482 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9997

lemma sg31483 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9997

lemma sg31484 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10461

lemma sg31485 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10006

lemma sg31486 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9350

lemma sg31487 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9998

lemma sg31488 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9998

lemma sg31489 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8726 sg9605

lemma sg31490 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,5,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9605

lemma sg31491 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10464

lemma sg31492 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10007

lemma sg31493 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9354

lemma sg31494 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9999

lemma sg31495 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9999

lemma sg31496 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14522

lemma sg31497 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11350

lemma sg31498 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10438

lemma sg31499 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9331

lemma sg31500 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10465

lemma sg31501 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10008

lemma sg31502 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10466

lemma sg31503 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10009

lemma sg31504 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9356

lemma sg31505 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10000

lemma sg31506 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg10000

lemma sg31507 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9997

lemma sg31508 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9649

lemma sg31509 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10447

lemma sg31510 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9357

lemma sg31511 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10001

lemma sg31512 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg10001

lemma sg31513 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9998

lemma sg31514 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9650

lemma sg31515 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4576 sg13500

lemma sg31516 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6993 sg11471

lemma sg31517 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6953 sg11477

lemma sg31518 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10523

lemma sg31519 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9393

lemma sg31520 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10835

lemma sg31521 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10523

lemma sg31522 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10467

lemma sg31523 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10010

lemma sg31524 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9358

lemma sg31525 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10002

lemma sg31526 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg10002

lemma sg31527 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10449

lemma sg31528 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9359

lemma sg31529 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10003

lemma sg31530 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg10003

lemma sg31531 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9341

lemma sg31532 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9342

lemma sg31533 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9342

lemma sg31534 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,7,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8832 sg9260

lemma sg31535 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10474

lemma sg31536 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,4,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10012

lemma sg31537 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10477

lemma sg31538 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10013

lemma sg31539 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9372

lemma sg31540 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10004

lemma sg31541 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg10004

lemma sg31542 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14523

lemma sg31543 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6953 sg11478

lemma sg31544 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9348

lemma sg31545 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9343

lemma sg31546 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10478

lemma sg31547 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10014

lemma sg31548 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10479

lemma sg31549 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10015

lemma sg31550 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9374

lemma sg31551 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10005

lemma sg31552 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg10005

lemma sg31553 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9349

lemma sg31554 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10461

lemma sg31555 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9375

lemma sg31556 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10006

lemma sg31557 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg10006

lemma sg31558 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,5,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9350

lemma sg31559 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3889 sg14517

lemma sg31560 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6602 sg11543

lemma sg31561 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10456

lemma sg31562 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9345

lemma sg31563 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10481

lemma sg31564 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10016

lemma sg31565 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10482

lemma sg31566 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10017

lemma sg31567 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9376

lemma sg31568 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10007

lemma sg31569 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg10007

lemma sg31570 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg10004

lemma sg31571 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4577 sg13500

lemma sg31572 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6604 sg11543

lemma sg31573 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8166 sg11054

lemma sg31574 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10531

lemma sg31575 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9402

lemma sg31576 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10836

lemma sg31577 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10531

lemma sg31578 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10483

lemma sg31579 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10018

lemma sg31580 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9377

lemma sg31581 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10008

lemma sg31582 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10466

lemma sg31583 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9378

lemma sg31584 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10009

lemma sg31585 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg10005

lemma sg31586 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9405

lemma sg31587 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg10006

lemma sg31588 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6605 sg11543

lemma sg31589 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8167 sg11054

lemma sg31590 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10484

lemma sg31591 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10484

lemma sg31592 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10019

lemma sg31593 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10484

lemma sg31594 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10467

lemma sg31595 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9379

lemma sg31596 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10010

lemma sg31597 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9358

lemma sg31598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9359

lemma sg31599 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9359

lemma sg31600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,8,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg10006

lemma sg31601 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,9,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10490

lemma sg31602 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,9,4,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10020

lemma sg31603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,9,4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9384

lemma sg31604 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,9,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10012

lemma sg31605 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3893 sg14520

lemma sg31606 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6999 sg11476

lemma sg31607 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9382

lemma sg31608 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9380

lemma sg31609 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9384

lemma sg31610 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10021

lemma sg31611 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10499

lemma sg31612 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10022

lemma sg31613 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9384

lemma sg31614 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10020

lemma sg31615 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [11,10,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9384

lemma sg31616 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,5,5,5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10504

lemma sg31617 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,5,5,5,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10023

lemma sg31618 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,5,5,5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10505

lemma sg31619 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,5,5,5,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10024

lemma sg31620 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,5,5,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8434 sg10428

lemma sg31621 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,5,5,5,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8723 sg9648

lemma sg31622 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,5,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8399 sg10655

lemma sg31623 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10507

lemma sg31624 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10025

lemma sg31625 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10508

lemma sg31626 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10026

lemma sg31627 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9394

lemma sg31628 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10023

lemma sg31629 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10509

lemma sg31630 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10027

lemma sg31631 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9395

lemma sg31632 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10024

lemma sg31633 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,5,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8726 sg9648

lemma sg31634 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10510

lemma sg31635 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10028

lemma sg31636 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9396

lemma sg31637 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9396

lemma sg31638 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5144 sg12697

lemma sg31639 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8769 sg9594

lemma sg31640 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10503

lemma sg31641 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9390

lemma sg31642 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10511

lemma sg31643 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10029

lemma sg31644 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10512

lemma sg31645 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10030

lemma sg31646 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9397

lemma sg31647 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9397

lemma sg31648 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg10023

lemma sg31649 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9398

lemma sg31650 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9398

lemma sg31651 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9398

lemma sg31652 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg10024

lemma sg31653 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10384

lemma sg31654 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8770 sg9594

lemma sg31655 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7456 sg11349

lemma sg31656 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10549

lemma sg31657 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9423

lemma sg31658 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10837

lemma sg31659 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10513

lemma sg31660 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10031

lemma sg31661 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9399

lemma sg31662 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9399

lemma sg31663 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9400

lemma sg31664 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9400

lemma sg31665 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9400

lemma sg31666 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,6,6,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8871 sg9155

lemma sg31667 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10515

lemma sg31668 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,4,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10032

lemma sg31669 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10517

lemma sg31670 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10033

lemma sg31671 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9403

lemma sg31672 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10025

lemma sg31673 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5144 sg12698

lemma sg31674 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11352

lemma sg31675 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9393

lemma sg31676 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9391

lemma sg31677 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10518

lemma sg31678 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10034

lemma sg31679 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10519

lemma sg31680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10035

lemma sg31681 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9404

lemma sg31682 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10026

lemma sg31683 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10509

lemma sg31684 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9405

lemma sg31685 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10027

lemma sg31686 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3889 sg14522

lemma sg31687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11353

lemma sg31688 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10506

lemma sg31689 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9392

lemma sg31690 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10520

lemma sg31691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10036

lemma sg31692 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10521

lemma sg31693 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10037

lemma sg31694 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9406

lemma sg31695 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10028

lemma sg31696 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4576 sg13502

lemma sg31697 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11354

lemma sg31698 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8166 sg11055

lemma sg31699 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10552

lemma sg31700 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9426

lemma sg31701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10838

lemma sg31702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10522

lemma sg31703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10038

lemma sg31704 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9407

lemma sg31705 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10512

lemma sg31706 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9408

lemma sg31707 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9429

lemma sg31708 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11355

lemma sg31709 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8167 sg11055

lemma sg31710 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10523

lemma sg31711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10523

lemma sg31712 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10039

lemma sg31713 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10513

lemma sg31714 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9409

lemma sg31715 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9400

lemma sg31716 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10525

lemma sg31717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,4,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10040

lemma sg31718 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9412

lemma sg31719 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3889 sg14523

lemma sg31720 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11356

lemma sg31721 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10514

lemma sg31722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9401

lemma sg31723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10526

lemma sg31724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10041

lemma sg31725 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10527

lemma sg31726 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10042

lemma sg31727 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9413

lemma sg31728 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4576 sg13503

lemma sg31729 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11357

lemma sg31730 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8168 sg11054

lemma sg31731 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10556

lemma sg31732 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9434

lemma sg31733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10839

lemma sg31734 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10528

lemma sg31735 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9414

lemma sg31736 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10519

lemma sg31737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9415

lemma sg31738 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,5,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9405

lemma sg31739 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3895 sg14522

end UniversalTensorSquare
end
end

end OAI
