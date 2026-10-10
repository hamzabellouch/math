import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 65. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26540 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8538 sg10108

lemma sg26541 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8385 sg10602

lemma sg26542 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9727

lemma sg26543 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8531 sg10115

lemma sg26544 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10115

lemma sg26545 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9064

lemma sg26546 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9493

lemma sg26547 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9727

lemma sg26548 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10298

lemma sg26549 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1723 sg18244

lemma sg26550 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1830 sg17109

lemma sg26551 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2197 sg15563

lemma sg26552 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2234 sg15520

lemma sg26553 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2678 sg15014

lemma sg26554 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2868 sg14855

lemma sg26555 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3518 sg14680

lemma sg26556 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14683

lemma sg26557 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5628 sg12603

lemma sg26558 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg971 sg21120

lemma sg26559 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2198 sg15563

lemma sg26560 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2235 sg15520

lemma sg26561 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2679 sg15014

lemma sg26562 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14855

lemma sg26563 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5250 sg12690

lemma sg26564 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2666 sg15023

lemma sg26565 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9207

lemma sg26566 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1296 sg20996

lemma sg26567 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8666 sg9701

lemma sg26568 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14510

lemma sg26569 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2671 sg15020

lemma sg26570 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6949 sg11469

lemma sg26571 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5965 sg11834

lemma sg26572 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9208

lemma sg26573 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9272

lemma sg26574 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8729 sg9508

lemma sg26575 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5547 sg12628

lemma sg26576 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5966 sg11834

lemma sg26577 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9209

lemma sg26578 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9187

lemma sg26579 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9825

lemma sg26580 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9508

lemma sg26581 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9210

lemma sg26582 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9188

lemma sg26583 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10722

lemma sg26584 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8720 sg9563

lemma sg26585 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9865

lemma sg26586 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10144

lemma sg26587 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9865

lemma sg26588 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8847 sg9160

lemma sg26589 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15520

lemma sg26590 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14510

lemma sg26591 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2870 sg14855

lemma sg26592 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6950 sg11469

lemma sg26593 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5997 sg11829

lemma sg26594 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9219

lemma sg26595 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9272

lemma sg26596 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9508

lemma sg26597 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3766 sg14540

lemma sg26598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6951 sg11469

lemma sg26599 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5967 sg11834

lemma sg26600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10299

lemma sg26601 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9273

lemma sg26602 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9825

lemma sg26603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9508

lemma sg26604 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5968 sg11834

lemma sg26605 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10300

lemma sg26606 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9209

lemma sg26607 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10723

lemma sg26608 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9563

lemma sg26609 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9210

lemma sg26610 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9866

lemma sg26611 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10145

lemma sg26612 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9866

lemma sg26613 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9836

lemma sg26614 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8803 sg9219

lemma sg26615 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9121

lemma sg26616 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6952 sg11469

lemma sg26617 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5969 sg11834

lemma sg26618 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9214

lemma sg26619 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9274

lemma sg26620 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10724

lemma sg26621 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8722 sg9563

lemma sg26622 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8443 sg10242

lemma sg26623 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9275

lemma sg26624 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9867

lemma sg26625 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10146

lemma sg26626 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9867

lemma sg26627 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9837

lemma sg26628 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9837

lemma sg26629 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10695

lemma sg26630 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10299

lemma sg26631 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9122

lemma sg26632 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10620

lemma sg26633 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9838

lemma sg26634 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9838

lemma sg26635 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8818 sg9187

lemma sg26636 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9564

lemma sg26637 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10300

lemma sg26638 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9123

lemma sg26639 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg9053

lemma sg26640 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9210

lemma sg26641 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9054

lemma sg26642 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14510

lemma sg26643 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3767 sg14540

lemma sg26644 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6953 sg11469

lemma sg26645 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5998 sg11829

lemma sg26646 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10301

lemma sg26647 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9273

lemma sg26648 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9207

lemma sg26649 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9481

lemma sg26650 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6954 sg11469

lemma sg26651 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5970 sg11834

lemma sg26652 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10302

lemma sg26653 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9276

lemma sg26654 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10725

lemma sg26655 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8812 sg9207

lemma sg26656 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10303

lemma sg26657 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9275

lemma sg26658 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9868

lemma sg26659 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10147

lemma sg26660 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9868

lemma sg26661 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9839

lemma sg26662 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9839

lemma sg26663 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10696

lemma sg26664 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10301

lemma sg26665 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9124

lemma sg26666 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5971 sg11834

lemma sg26667 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10304

lemma sg26668 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9277

lemma sg26669 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9869

lemma sg26670 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10148

lemma sg26671 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9869

lemma sg26672 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9278

lemma sg26673 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9840

lemma sg26674 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9840

lemma sg26675 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10697

lemma sg26676 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9565

lemma sg26677 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10302

lemma sg26678 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9125

lemma sg26679 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10692

lemma sg26680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9831

lemma sg26681 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9566

lemma sg26682 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10303

lemma sg26683 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9126

lemma sg26684 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10300

lemma sg26685 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10693

lemma sg26686 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8582 sg10088

lemma sg26687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9279

lemma sg26688 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9841

lemma sg26689 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9841

lemma sg26690 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10698

lemma sg26691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9832

lemma sg26692 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9567

lemma sg26693 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10304

lemma sg26694 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9127

lemma sg26695 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9214

lemma sg26696 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9058

lemma sg26697 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8730 sg9515

lemma sg26698 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9515

lemma sg26699 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10621

lemma sg26700 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3768 sg14540

lemma sg26701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5565 sg12621

lemma sg26702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5999 sg11829

lemma sg26703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10305

lemma sg26704 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9276

lemma sg26705 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10726

lemma sg26706 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8819 sg9189

lemma sg26707 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6000 sg11829

lemma sg26708 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10306

lemma sg26709 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9280

lemma sg26710 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9870

lemma sg26711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10149

lemma sg26712 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9870

lemma sg26713 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9278

lemma sg26714 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9842

lemma sg26715 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9842

lemma sg26716 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10699

lemma sg26717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9568

lemma sg26718 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10305

lemma sg26719 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9128

lemma sg26720 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10694

lemma sg26721 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10307

lemma sg26722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9281

lemma sg26723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9843

lemma sg26724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9843

lemma sg26725 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10700

lemma sg26726 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9834

lemma sg26727 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9569

lemma sg26728 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10306

lemma sg26729 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9129

lemma sg26730 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10302

lemma sg26731 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9566

lemma sg26732 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10303

lemma sg26733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9282

lemma sg26734 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9835

lemma sg26735 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9570

lemma sg26736 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10307

lemma sg26737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9130

lemma sg26738 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9567

lemma sg26739 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10304

lemma sg26740 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10303

lemma sg26741 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8762 sg9451

lemma sg26742 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8534 sg10115

lemma sg26743 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10115

lemma sg26744 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10304

lemma sg26745 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5577 sg12618

lemma sg26746 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6001 sg11829

lemma sg26747 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9227

lemma sg26748 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9280

lemma sg26749 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9215

lemma sg26750 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10150

lemma sg26751 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8573 sg10095

lemma sg26752 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9228

lemma sg26753 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9227

lemma sg26754 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9833

lemma sg26755 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10136

lemma sg26756 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8370 sg10635

lemma sg26757 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9227

lemma sg26758 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9227

lemma sg26759 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9227

lemma sg26760 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9076

lemma sg26761 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10305

lemma sg26762 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9228

lemma sg26763 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9228

lemma sg26764 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9228

lemma sg26765 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9228

lemma sg26766 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9077

lemma sg26767 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9569

lemma sg26768 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10306

lemma sg26769 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8813 sg9217

lemma sg26770 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9835

lemma sg26771 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9570

lemma sg26772 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10307

lemma sg26773 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10306

lemma sg26774 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9570

lemma sg26775 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10307

lemma sg26776 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,7,7,7,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8540 sg10115

lemma sg26777 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1831 sg17109

lemma sg26778 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2199 sg15563

lemma sg26779 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1853 sg16201

lemma sg26780 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2234 sg15521

lemma sg26781 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2874 sg14852

lemma sg26782 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3519 sg14680

lemma sg26783 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg971 sg21121

lemma sg26784 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5482 sg12648

lemma sg26785 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg971 sg21122

lemma sg26786 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6362 sg11739

lemma sg26787 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2242 sg15515

lemma sg26788 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2687 sg15012

lemma sg26789 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2875 sg14852

lemma sg26790 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4680 sg12940

lemma sg26791 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5250 sg12691

lemma sg26792 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9219

lemma sg26793 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8193 sg10854

lemma sg26794 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8666 sg9713

lemma sg26795 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3766 sg14541

lemma sg26796 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5268 sg12683

lemma sg26797 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6002 sg11828

lemma sg26798 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6756 sg11508

lemma sg26799 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9283

lemma sg26800 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9714

lemma sg26801 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8758 sg9457

lemma sg26802 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5252 sg12691

lemma sg26803 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9220

lemma sg26804 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8242 sg10848

lemma sg26805 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9715

lemma sg26806 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8534 sg10116

lemma sg26807 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8243 sg10848

lemma sg26808 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9716

lemma sg26809 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10151

lemma sg26810 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8535 sg10116

lemma sg26811 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8758 sg9458

lemma sg26812 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9065

lemma sg26813 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9131

lemma sg26814 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2688 sg15012

lemma sg26815 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3767 sg14541

lemma sg26816 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5268 sg12684

lemma sg26817 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6002 sg11829

lemma sg26818 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6757 sg11508

lemma sg26819 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9283

lemma sg26820 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9717

lemma sg26821 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8742 sg9481

lemma sg26822 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5269 sg12683

lemma sg26823 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6003 sg11828

lemma sg26824 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9221

lemma sg26825 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9284

lemma sg26826 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9219

lemma sg26827 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8537 sg10116

lemma sg26828 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9222

lemma sg26829 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9220

lemma sg26830 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9836

lemma sg26831 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10152

lemma sg26832 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8538 sg10116

lemma sg26833 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9720

lemma sg26834 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9571

lemma sg26835 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8809 sg9219

lemma sg26836 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8759 sg9458

lemma sg26837 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9132

lemma sg26838 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6004 sg11828

lemma sg26839 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9223

lemma sg26840 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9285

lemma sg26841 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9871

lemma sg26842 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10153

lemma sg26843 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9871

lemma sg26844 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9286

lemma sg26845 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9837

lemma sg26846 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8730 sg9520

lemma sg26847 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9187

lemma sg26848 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9572

lemma sg26849 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9520

lemma sg26850 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9133

lemma sg26851 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg9067

lemma sg26852 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9838

lemma sg26853 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9573

lemma sg26854 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8840 sg9166

lemma sg26855 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9134

lemma sg26856 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9220

lemma sg26857 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3768 sg14541

lemma sg26858 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5269 sg12684

lemma sg26859 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6003 sg11829

lemma sg26860 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9224

lemma sg26861 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9284

lemma sg26862 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9219

lemma sg26863 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8742 sg9484

lemma sg26864 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6004 sg11829

lemma sg26865 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9225

lemma sg26866 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9287

lemma sg26867 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9872

lemma sg26868 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10154

lemma sg26869 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9872

lemma sg26870 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9286

lemma sg26871 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9839

lemma sg26872 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9571

lemma sg26873 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8813 sg9219

lemma sg26874 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9574

lemma sg26875 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9522

lemma sg26876 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9135

lemma sg26877 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9226

lemma sg26878 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9288

lemma sg26879 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9837

lemma sg26880 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9571

lemma sg26881 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8814 sg9219

lemma sg26882 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9840

lemma sg26883 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9575

lemma sg26884 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8734 sg9520

lemma sg26885 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9136

lemma sg26886 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9221

lemma sg26887 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9573

lemma sg26888 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9222

lemma sg26889 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9289

lemma sg26890 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9841

lemma sg26891 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9576

lemma sg26892 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8735 sg9520

lemma sg26893 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9137

lemma sg26894 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8808 sg9223

lemma sg26895 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9223

lemma sg26896 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10626

lemma sg26897 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5270 sg12684

lemma sg26898 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6005 sg11829

lemma sg26899 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9227

lemma sg26900 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9287

lemma sg26901 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9873

lemma sg26902 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10155

lemma sg26903 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9873

lemma sg26904 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9228

lemma sg26905 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9290

lemma sg26906 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9839

lemma sg26907 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8733 sg9522

lemma sg26908 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9194

lemma sg26909 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9842

lemma sg26910 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9577

lemma sg26911 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8734 sg9522

lemma sg26912 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9138

lemma sg26913 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9224

lemma sg26914 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9291

lemma sg26915 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9843

lemma sg26916 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9578

lemma sg26917 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8735 sg9522

lemma sg26918 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9139

lemma sg26919 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9575

lemma sg26920 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9225

lemma sg26921 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8813 sg9222

lemma sg26922 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9841

lemma sg26923 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9576

lemma sg26924 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9226

lemma sg26925 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8813 sg9223

lemma sg26926 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9576

lemma sg26927 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8814 sg9223

lemma sg26928 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6006 sg11829

lemma sg26929 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8265 sg10845

lemma sg26930 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9290

lemma sg26931 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9224

lemma sg26932 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8760 sg9459

lemma sg26933 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8823 sg9194

lemma sg26934 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9292

lemma sg26935 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9842

lemma sg26936 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9579

lemma sg26937 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8823 sg9195

lemma sg26938 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9140

lemma sg26939 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,8,7,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9577

end UniversalTensorSquare
end
end

end OAI
