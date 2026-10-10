import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes50
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
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes48

namespace OAI

/-! Semigroup Nodes 90. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg36541 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18432

lemma sg36542 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19839

lemma sg36543 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18432

lemma sg36544 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19839

lemma sg36545 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18435

lemma sg36546 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15844

lemma sg36547 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19841

lemma sg36548 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18433

lemma sg36549 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17419

lemma sg36550 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18981

lemma sg36551 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18433

lemma sg36552 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19840

lemma sg36553 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18433

lemma sg36554 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19840

lemma sg36555 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18981

lemma sg36556 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18434

lemma sg36557 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19841

lemma sg36558 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18434

lemma sg36559 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19841

lemma sg36560 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18434

lemma sg36561 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19841

lemma sg36562 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17420

lemma sg36563 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19298

lemma sg36564 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18982

lemma sg36565 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17373

lemma sg36566 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18917 sg19667

lemma sg36567 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18436

lemma sg36568 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19842

lemma sg36569 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15845

lemma sg36570 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19668

lemma sg36571 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17374

lemma sg36572 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18435

lemma sg36573 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19842

lemma sg36574 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18435

lemma sg36575 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19842

lemma sg36576 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18435

lemma sg36577 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19842

lemma sg36578 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17421

lemma sg36579 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19299

lemma sg36580 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18983

lemma sg36581 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17422

lemma sg36582 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18984

lemma sg36583 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17422

lemma sg36584 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19300

lemma sg36585 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18984

lemma sg36586 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17375

lemma sg36587 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18948

lemma sg36588 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18051

lemma sg36589 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16796

lemma sg36590 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18285 sg20369

lemma sg36591 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17376

lemma sg36592 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18286 sg20369

lemma sg36593 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17731

lemma sg36594 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18436

lemma sg36595 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17423

lemma sg36596 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18436

lemma sg36597 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16403

lemma sg36598 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18112 sg20493

lemma sg36599 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18436

lemma sg36600 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20579

lemma sg36601 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18436

lemma sg36602 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg20712 sg16269

lemma sg36603 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16809

lemma sg36604 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17423

lemma sg36605 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19616 sg19301

lemma sg36606 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19301

lemma sg36607 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17423

lemma sg36608 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19301

lemma sg36609 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19301

lemma sg36610 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17377

lemma sg36611 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18113 sg20481

lemma sg36612 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18052

lemma sg36613 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16797

lemma sg36614 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20528 sg17244

lemma sg36615 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17378

lemma sg36616 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18113 sg20482

lemma sg36617 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16692

lemma sg36618 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16692

lemma sg36619 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20641 sg16692

lemma sg36620 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20645 sg16691

lemma sg36621 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15846

lemma sg36622 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18437

lemma sg36623 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17424

lemma sg36624 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18985

lemma sg36625 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20804 sg16163

lemma sg36626 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18437

lemma sg36627 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19843

lemma sg36628 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18437

lemma sg36629 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19843

lemma sg36630 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,5,5,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18985

lemma sg36631 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15819

lemma sg36632 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15847

lemma sg36633 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19669

lemma sg36634 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17379

lemma sg36635 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16405

lemma sg36636 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18438

lemma sg36637 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18439

lemma sg36638 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18438

lemma sg36639 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19844

lemma sg36640 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18438

lemma sg36641 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19844

lemma sg36642 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18439

lemma sg36643 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19845

lemma sg36644 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18439

lemma sg36645 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19845

lemma sg36646 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,5,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18986

lemma sg36647 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15820

lemma sg36648 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18204

lemma sg36649 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17365

lemma sg36650 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18443

lemma sg36651 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18440

lemma sg36652 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15848

lemma sg36653 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18440

lemma sg36654 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19846

lemma sg36655 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18440

lemma sg36656 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19846

lemma sg36657 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16405

lemma sg36658 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18441

lemma sg36659 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17425

lemma sg36660 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18987

lemma sg36661 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18441

lemma sg36662 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19847

lemma sg36663 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18441

lemma sg36664 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19847

lemma sg36665 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18987

lemma sg36666 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17426

lemma sg36667 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19302

lemma sg36668 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18988

lemma sg36669 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20792 sg16180

lemma sg36670 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15849

lemma sg36671 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19849

lemma sg36672 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18442

lemma sg36673 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17427

lemma sg36674 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19576 sg19591

lemma sg36675 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18442

lemma sg36676 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19848

lemma sg36677 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18442

lemma sg36678 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19848

lemma sg36679 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19303

lemma sg36680 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18443

lemma sg36681 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19849

lemma sg36682 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18443

lemma sg36683 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19849

lemma sg36684 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18443

lemma sg36685 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19849

lemma sg36686 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17428

lemma sg36687 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19304

lemma sg36688 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18989

lemma sg36689 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17381

lemma sg36690 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18952

lemma sg36691 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17429

lemma sg36692 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19616 sg19305

lemma sg36693 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17429

lemma sg36694 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19305

lemma sg36695 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19305

lemma sg36696 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17382

lemma sg36697 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,6,6,6,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18286 sg20370

lemma sg36698 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,4,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg15813

lemma sg36699 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15822

lemma sg36700 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18205

lemma sg36701 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17368

lemma sg36702 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16406

lemma sg36703 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18444

lemma sg36704 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15851

lemma sg36705 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18444

lemma sg36706 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19850

lemma sg36707 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18444

lemma sg36708 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19850

lemma sg36709 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20690 sg16390

lemma sg36710 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18445

lemma sg36711 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17430

lemma sg36712 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18990

lemma sg36713 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18445

lemma sg36714 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19851

lemma sg36715 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18445

lemma sg36716 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19851

lemma sg36717 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18990

lemma sg36718 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17431

lemma sg36719 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19306

lemma sg36720 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,5,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18991

lemma sg36721 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18448

lemma sg36722 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18446

lemma sg36723 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15823

lemma sg36724 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18446

lemma sg36725 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19852

lemma sg36726 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18446

lemma sg36727 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19852

lemma sg36728 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18449

lemma sg36729 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15852

lemma sg36730 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19854

lemma sg36731 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18447

lemma sg36732 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17432

lemma sg36733 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18992

lemma sg36734 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18447

lemma sg36735 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19853

lemma sg36736 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18447

lemma sg36737 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19853

lemma sg36738 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18992

lemma sg36739 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18448

lemma sg36740 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19854

lemma sg36741 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18448

lemma sg36742 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19854

lemma sg36743 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18448

lemma sg36744 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19854

lemma sg36745 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17433

lemma sg36746 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19307

lemma sg36747 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18993

lemma sg36748 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17384

lemma sg36749 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18955

lemma sg36750 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16409

lemma sg36751 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19855

lemma sg36752 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15853

lemma sg36753 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19670

lemma sg36754 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17385

lemma sg36755 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18449

lemma sg36756 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19855

lemma sg36757 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18449

lemma sg36758 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19855

lemma sg36759 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18449

lemma sg36760 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19855

lemma sg36761 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17434

lemma sg36762 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19308

lemma sg36763 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18994

lemma sg36764 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17435

lemma sg36765 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18995

lemma sg36766 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17435

lemma sg36767 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19309

lemma sg36768 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18995

lemma sg36769 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17386

lemma sg36770 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18956

lemma sg36771 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18053

lemma sg36772 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16798

lemma sg36773 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18285 sg20371

lemma sg36774 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17387

lemma sg36775 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,6,6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18286 sg20371

lemma sg36776 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18451

lemma sg36777 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15854

lemma sg36778 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16407

lemma sg36779 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18450

lemma sg36780 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17436

lemma sg36781 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18996

lemma sg36782 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18450

lemma sg36783 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19856

lemma sg36784 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18450

lemma sg36785 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19856

lemma sg36786 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18996

lemma sg36787 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18452

lemma sg36788 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19857

lemma sg36789 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15855

lemma sg36790 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19671

lemma sg36791 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17388

lemma sg36792 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18451

lemma sg36793 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19857

lemma sg36794 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18451

lemma sg36795 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19857

lemma sg36796 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18451

lemma sg36797 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19857

lemma sg36798 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17437

lemma sg36799 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19310

lemma sg36800 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18997

lemma sg36801 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17438

lemma sg36802 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18998

lemma sg36803 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17438

lemma sg36804 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19311

lemma sg36805 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18998

lemma sg36806 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17389

lemma sg36807 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18958

lemma sg36808 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17746

lemma sg36809 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18452

lemma sg36810 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18281 sg20401

lemma sg36811 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18452

lemma sg36812 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg16649 sg20680

lemma sg36813 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18282 sg20401

lemma sg36814 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18452

lemma sg36815 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20580

lemma sg36816 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18452

lemma sg36817 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg16650 sg20680

lemma sg36818 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16813

lemma sg36819 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17439

lemma sg36820 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18999

lemma sg36821 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19312

lemma sg36822 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17439

lemma sg36823 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19312

lemma sg36824 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18999

lemma sg36825 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17390

lemma sg36826 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18959

lemma sg36827 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg18960

lemma sg36828 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16799

lemma sg36829 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18916 sg19672

lemma sg36830 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17391

lemma sg36831 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18960

lemma sg36832 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16796

lemma sg36833 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17376

lemma sg36834 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17440

lemma sg36835 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15856

lemma sg36836 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16409

lemma sg36837 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16814

lemma sg36838 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17440

lemma sg36839 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20496 sg18109

lemma sg36840 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19575 sg19612

lemma sg36841 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17440

lemma sg36842 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20319 sg18306

lemma sg36843 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20320 sg18306

lemma sg36844 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18054

lemma sg36845 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16800

lemma sg36846 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20528 sg17245

lemma sg36847 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17392

lemma sg36848 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16797

lemma sg36849 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17378

lemma sg36850 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,7,7,7,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20716 sg16270

lemma sg36851 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,4,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20863 sg15725

lemma sg36852 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,4,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20694 sg16386

lemma sg36853 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,4,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20695 sg16386

lemma sg36854 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18455

lemma sg36855 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18453

lemma sg36856 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15828

lemma sg36857 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18453

lemma sg36858 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19858

lemma sg36859 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18453

lemma sg36860 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19858

lemma sg36861 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16412

lemma sg36862 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15857

lemma sg36863 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19860

lemma sg36864 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18454

lemma sg36865 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17441

lemma sg36866 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19000

lemma sg36867 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18454

lemma sg36868 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19859

lemma sg36869 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18454

lemma sg36870 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19859

lemma sg36871 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg19000

lemma sg36872 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18455

lemma sg36873 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19860

lemma sg36874 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18455

lemma sg36875 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19860

lemma sg36876 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18455

lemma sg36877 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19860

lemma sg36878 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17442

lemma sg36879 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19313

lemma sg36880 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg19001

lemma sg36881 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17394

lemma sg36882 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,5,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18962

lemma sg36883 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18457

lemma sg36884 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15858

lemma sg36885 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16411

lemma sg36886 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18456

lemma sg36887 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17443

lemma sg36888 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19002

lemma sg36889 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18456

lemma sg36890 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19861

lemma sg36891 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18456

lemma sg36892 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19861

lemma sg36893 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg19002

lemma sg36894 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18458

lemma sg36895 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19862

lemma sg36896 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15859

lemma sg36897 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19673

lemma sg36898 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17395

lemma sg36899 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18457

lemma sg36900 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19862

lemma sg36901 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18457

lemma sg36902 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19862

lemma sg36903 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18457

lemma sg36904 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19862

lemma sg36905 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17444

lemma sg36906 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19314

lemma sg36907 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg19003

lemma sg36908 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17445

lemma sg36909 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19004

lemma sg36910 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17445

lemma sg36911 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19315

lemma sg36912 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg19004

lemma sg36913 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17396

lemma sg36914 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18964

lemma sg36915 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17751

lemma sg36916 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19863

lemma sg36917 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19863

lemma sg36918 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18458

lemma sg36919 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19863

lemma sg36920 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19863

lemma sg36921 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18458

lemma sg36922 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19863

lemma sg36923 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18458

lemma sg36924 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19863

lemma sg36925 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16816

lemma sg36926 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17446

lemma sg36927 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg19005

lemma sg36928 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19316

lemma sg36929 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17446

lemma sg36930 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19316

lemma sg36931 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg19005

lemma sg36932 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17397

lemma sg36933 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19624 sg18965

lemma sg36934 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg18966

lemma sg36935 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16801

lemma sg36936 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18916 sg19674

lemma sg36937 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17398

lemma sg36938 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16695

lemma sg36939 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,6,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16695

lemma sg36940 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,9,8,8,7,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18459

end UniversalTensorSquare
end
end

end OAI
