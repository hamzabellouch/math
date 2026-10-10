import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes50
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes47
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes49
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes43
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes46
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes38
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes40
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes42
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes45
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes48

namespace OAI

/-! Semigroup Nodes 95. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg38541 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19019

lemma sg38542 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16822

lemma sg38543 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17462

lemma sg38544 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17541

lemma sg38545 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15920

lemma sg38546 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16457

lemma sg38547 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16858

lemma sg38548 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17541

lemma sg38549 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19576 sg19601

lemma sg38550 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19380

lemma sg38551 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17541

lemma sg38552 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19020

lemma sg38553 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16823

lemma sg38554 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17463

lemma sg38555 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16811

lemma sg38556 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17435

lemma sg38557 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,6,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16405

lemma sg38558 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20684 sg16464

lemma sg38559 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18549

lemma sg38560 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16859

lemma sg38561 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16458

lemma sg38562 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15870

lemma sg38563 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17436

lemma sg38564 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18213

lemma sg38565 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17436

lemma sg38566 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17806

lemma sg38567 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19952

lemma sg38568 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19952

lemma sg38569 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18549

lemma sg38570 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19952

lemma sg38571 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19952

lemma sg38572 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18549

lemma sg38573 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19952

lemma sg38574 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18549

lemma sg38575 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16859

lemma sg38576 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17542

lemma sg38577 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19063

lemma sg38578 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19381

lemma sg38579 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17542

lemma sg38580 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17464

lemma sg38581 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17543

lemma sg38582 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15921

lemma sg38583 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16459

lemma sg38584 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16860

lemma sg38585 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17543

lemma sg38586 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19064

lemma sg38587 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19382

lemma sg38588 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17543

lemma sg38589 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19022

lemma sg38590 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16824

lemma sg38591 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17465

lemma sg38592 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16812

lemma sg38593 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17438

lemma sg38594 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17466

lemma sg38595 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18284 sg20379

lemma sg38596 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17466

lemma sg38597 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18065

lemma sg38598 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16825

lemma sg38599 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17466

lemma sg38600 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16813

lemma sg38601 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17439

lemma sg38602 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16280

lemma sg38603 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17440

lemma sg38604 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18214

lemma sg38605 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16814

lemma sg38606 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17440

lemma sg38607 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,7,7,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16281

lemma sg38608 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16460

lemma sg38609 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15922

lemma sg38610 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20689 sg16423

lemma sg38611 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20690 sg16423

lemma sg38612 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18550

lemma sg38613 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16861

lemma sg38614 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17544

lemma sg38615 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19065

lemma sg38616 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19953

lemma sg38617 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18550

lemma sg38618 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19953

lemma sg38619 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18550

lemma sg38620 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19953

lemma sg38621 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18551

lemma sg38622 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15872

lemma sg38623 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18552

lemma sg38624 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17807

lemma sg38625 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19954

lemma sg38626 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15923

lemma sg38627 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17467

lemma sg38628 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19692

lemma sg38629 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17467

lemma sg38630 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19954

lemma sg38631 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18551

lemma sg38632 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19954

lemma sg38633 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19954

lemma sg38634 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18551

lemma sg38635 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19954

lemma sg38636 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18551

lemma sg38637 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19383

lemma sg38638 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17545

lemma sg38639 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17808

lemma sg38640 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19955

lemma sg38641 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19955

lemma sg38642 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18552

lemma sg38643 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19955

lemma sg38644 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19955

lemma sg38645 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18552

lemma sg38646 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19955

lemma sg38647 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18552

lemma sg38648 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16862

lemma sg38649 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17546

lemma sg38650 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19066

lemma sg38651 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19384

lemma sg38652 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17546

lemma sg38653 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17468

lemma sg38654 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19025

lemma sg38655 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16826

lemma sg38656 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,5,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17469

lemma sg38657 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16583

lemma sg38658 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18553

lemma sg38659 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16863

lemma sg38660 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16461

lemma sg38661 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15875

lemma sg38662 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17443

lemma sg38663 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18215

lemma sg38664 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17443

lemma sg38665 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17809

lemma sg38666 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19956

lemma sg38667 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19956

lemma sg38668 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18553

lemma sg38669 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19956

lemma sg38670 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19956

lemma sg38671 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18553

lemma sg38672 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19956

lemma sg38673 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18553

lemma sg38674 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16863

lemma sg38675 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17547

lemma sg38676 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19067

lemma sg38677 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19385

lemma sg38678 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17547

lemma sg38679 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17470

lemma sg38680 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17548

lemma sg38681 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15924

lemma sg38682 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16462

lemma sg38683 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16864

lemma sg38684 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17548

lemma sg38685 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19068

lemma sg38686 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19386

lemma sg38687 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17548

lemma sg38688 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19026

lemma sg38689 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16827

lemma sg38690 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17471

lemma sg38691 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16815

lemma sg38692 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17445

lemma sg38693 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17472

lemma sg38694 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19693

lemma sg38695 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17472

lemma sg38696 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18066

lemma sg38697 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16828

lemma sg38698 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17472

lemma sg38699 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16816

lemma sg38700 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17446

lemma sg38701 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,6,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16406

lemma sg38702 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17810

lemma sg38703 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18554

lemma sg38704 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17810

lemma sg38705 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19957

lemma sg38706 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19957

lemma sg38707 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18554

lemma sg38708 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19957

lemma sg38709 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19957

lemma sg38710 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18554

lemma sg38711 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19957

lemma sg38712 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18554

lemma sg38713 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17549

lemma sg38714 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15925

lemma sg38715 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16463

lemma sg38716 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16865

lemma sg38717 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17549

lemma sg38718 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19069

lemma sg38719 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19387

lemma sg38720 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17549

lemma sg38721 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19027

lemma sg38722 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16829

lemma sg38723 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17473

lemma sg38724 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17474

lemma sg38725 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19694

lemma sg38726 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17474

lemma sg38727 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19028

lemma sg38728 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16830

lemma sg38729 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17474

lemma sg38730 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16817

lemma sg38731 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17448

lemma sg38732 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16407

lemma sg38733 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17449

lemma sg38734 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18216

lemma sg38735 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16818

lemma sg38736 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17449

lemma sg38737 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16408

lemma sg38738 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17440

lemma sg38739 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16409

lemma sg38740 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,7,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16409

lemma sg38741 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16866

lemma sg38742 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16464

lemma sg38743 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17550

lemma sg38744 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15926

lemma sg38745 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16464

lemma sg38746 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16866

lemma sg38747 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17550

lemma sg38748 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19576 sg19602

lemma sg38749 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19388

lemma sg38750 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17550

lemma sg38751 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17475

lemma sg38752 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19695

lemma sg38753 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17475

lemma sg38754 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18067

lemma sg38755 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16831

lemma sg38756 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17475

lemma sg38757 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16819

lemma sg38758 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17450

lemma sg38759 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17451

lemma sg38760 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18217

lemma sg38761 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16820

lemma sg38762 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17451

lemma sg38763 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16286

lemma sg38764 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16287

lemma sg38765 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20870 sg15735

lemma sg38766 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16287

lemma sg38767 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17440

lemma sg38768 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17440

lemma sg38769 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,8,8,8,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20487

lemma sg38770 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18555

lemma sg38771 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15879

lemma sg38772 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16466

lemma sg38773 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17811

lemma sg38774 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19958

lemma sg38775 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15927

lemma sg38776 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17476

lemma sg38777 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18284 sg20380

lemma sg38778 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17476

lemma sg38779 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19958

lemma sg38780 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18555

lemma sg38781 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19958

lemma sg38782 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19958

lemma sg38783 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18555

lemma sg38784 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19958

lemma sg38785 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18555

lemma sg38786 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19389

lemma sg38787 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17551

lemma sg38788 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16585

lemma sg38789 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18556

lemma sg38790 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16867

lemma sg38791 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16465

lemma sg38792 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15880

lemma sg38793 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20709 sg16305

lemma sg38794 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20864 sg15750

lemma sg38795 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20865 sg15750

lemma sg38796 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17812

lemma sg38797 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19959

lemma sg38798 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19959

lemma sg38799 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18556

lemma sg38800 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19959

lemma sg38801 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19959

lemma sg38802 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18556

lemma sg38803 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19959

lemma sg38804 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18556

lemma sg38805 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16867

lemma sg38806 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17552

lemma sg38807 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19070

lemma sg38808 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19390

lemma sg38809 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17552

lemma sg38810 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17477

lemma sg38811 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17553

lemma sg38812 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15928

lemma sg38813 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16466

lemma sg38814 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16868

lemma sg38815 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17553

lemma sg38816 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19071

lemma sg38817 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19391

lemma sg38818 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17553

lemma sg38819 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19030

lemma sg38820 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16833

lemma sg38821 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17478

lemma sg38822 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16724

lemma sg38823 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,5,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16724

lemma sg38824 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17813

lemma sg38825 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18557

lemma sg38826 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17813

lemma sg38827 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19960

lemma sg38828 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19960

lemma sg38829 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18557

lemma sg38830 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19960

lemma sg38831 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19960

lemma sg38832 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18557

lemma sg38833 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19960

lemma sg38834 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18557

lemma sg38835 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17554

lemma sg38836 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15929

lemma sg38837 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16467

lemma sg38838 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16869

lemma sg38839 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17554

lemma sg38840 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19072

lemma sg38841 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19392

lemma sg38842 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17554

lemma sg38843 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19031

lemma sg38844 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16834

lemma sg38845 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17479

lemma sg38846 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17480

lemma sg38847 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19696

lemma sg38848 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17480

lemma sg38849 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19032

lemma sg38850 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16835

lemma sg38851 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17480

lemma sg38852 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16726

lemma sg38853 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16726

lemma sg38854 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16411

lemma sg38855 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16310

lemma sg38856 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20866 sg15753

lemma sg38857 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16727

lemma sg38858 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16727

lemma sg38859 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16412

lemma sg38860 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16870

lemma sg38861 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16468

lemma sg38862 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17555

lemma sg38863 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15930

lemma sg38864 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16468

lemma sg38865 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16870

lemma sg38866 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17555

lemma sg38867 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19073

lemma sg38868 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19393

lemma sg38869 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17555

lemma sg38870 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17481

lemma sg38871 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19697

lemma sg38872 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17481

lemma sg38873 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19033

lemma sg38874 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16836

lemma sg38875 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17481

lemma sg38876 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16728

lemma sg38877 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16728

lemma sg38878 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16312

lemma sg38879 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20866 sg15754

lemma sg38880 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16729

lemma sg38881 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16729

lemma sg38882 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16413

lemma sg38883 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17449

lemma sg38884 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16414

lemma sg38885 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16414

lemma sg38886 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20719 sg16285

lemma sg38887 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20872 sg15734

lemma sg38888 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17482

lemma sg38889 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15883

lemma sg38890 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20505 sg17482

lemma sg38891 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17482

lemma sg38892 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19698

lemma sg38893 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17482

lemma sg38894 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18068

lemma sg38895 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16837

lemma sg38896 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17482

lemma sg38897 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16313

lemma sg38898 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20866 sg15755

lemma sg38899 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16730

lemma sg38900 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16730

lemma sg38901 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16415

lemma sg38902 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17451

lemma sg38903 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16416

lemma sg38904 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16416

lemma sg38905 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17449

lemma sg38906 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17449

lemma sg38907 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,8,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20488

lemma sg38908 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20709 sg16314

lemma sg38909 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20864 sg15756

lemma sg38910 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20865 sg15756

lemma sg38911 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16314

lemma sg38912 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20866 sg15756

lemma sg38913 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16731

lemma sg38914 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16731

lemma sg38915 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20763 sg16267

lemma sg38916 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20838 sg16159

lemma sg38917 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20764 sg16267

lemma sg38918 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17451

lemma sg38919 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17451

lemma sg38920 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,10,9,9,9,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20489

lemma sg38921 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,5,5,5,5,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18558

lemma sg38922 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,5,5,5,5,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20840 sg16137

lemma sg38923 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,5,5,5,5,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18558

lemma sg38924 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,5,5,5,5,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19961

lemma sg38925 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,5,5,5,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18558

lemma sg38926 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,5,5,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20794 sg16176

lemma sg38927 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,5,5,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18559

lemma sg38928 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,5,5,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17563

lemma sg38929 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,5,5,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19074

lemma sg38930 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,5,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20814 sg16165

lemma sg38931 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,5,5,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18559

lemma sg38932 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,5,5,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19962

lemma sg38933 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,5,5,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18559

lemma sg38934 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,6,5,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15884

lemma sg38935 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,6,5,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15931

lemma sg38936 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,6,5,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19699

lemma sg38937 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,6,5,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17483

lemma sg38938 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,6,5,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16478

lemma sg38939 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,6,5,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18560

lemma sg38940 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,6,6,5,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18561

end UniversalTensorSquare
end
end

end OAI
