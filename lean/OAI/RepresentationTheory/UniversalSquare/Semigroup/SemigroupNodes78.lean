import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes49
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes57
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes38
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes40

namespace OAI

/-! Semigroup Nodes 78. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31740 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11358

lemma sg31741 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10516

lemma sg31742 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8660 sg9996

lemma sg31743 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10529

lemma sg31744 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10043

lemma sg31745 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4577 sg13502

lemma sg31746 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11359

lemma sg31747 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8169 sg11054

lemma sg31748 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10557

lemma sg31749 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9435

lemma sg31750 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10840

lemma sg31751 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10530

lemma sg31752 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9416

lemma sg31753 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10521

lemma sg31754 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9417

lemma sg31755 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11360

lemma sg31756 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8170 sg11054

lemma sg31757 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10531

lemma sg31758 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10531

lemma sg31759 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10522

lemma sg31760 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9418

lemma sg31761 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9436

lemma sg31762 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8171 sg11054

lemma sg31763 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10523

lemma sg31764 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9419

lemma sg31765 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,8,6,6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9409

lemma sg31766 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,9,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3893 sg14523

lemma sg31767 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,9,4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6999 sg11478

lemma sg31768 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,9,4,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9411

lemma sg31769 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,9,4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9410

lemma sg31770 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,9,4,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10533

lemma sg31771 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,9,4,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10534

lemma sg31772 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,9,4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9420

lemma sg31773 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3902 sg14520

lemma sg31774 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7013 sg11476

lemma sg31775 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10532

lemma sg31776 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8660 sg10011

lemma sg31777 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10536

lemma sg31778 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3893 sg14524

lemma sg31779 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7014 sg11476

lemma sg31780 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6999 sg11480

lemma sg31781 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10558

lemma sg31782 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9437

lemma sg31783 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10537

lemma sg31784 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9421

lemma sg31785 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10534

lemma sg31786 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,10,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9422

lemma sg31787 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,11,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1728 sg18255

lemma sg31788 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,11,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1837 sg17137

lemma sg31789 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,11,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3903 sg14520

lemma sg31790 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,11,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7016 sg11476

lemma sg31791 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,11,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8836 sg9380

lemma sg31792 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,11,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8774 sg9580

lemma sg31793 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,12,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg21111

lemma sg31794 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,12,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1841 sg17124

lemma sg31795 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,12,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1935 sg16123

lemma sg31796 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,12,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3178 sg14807

lemma sg31797 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,12,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3786 sg14545

lemma sg31798 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,12,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5889 sg11840

lemma sg31799 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,12,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6626 sg11542

lemma sg31800 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,12,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8611 sg10105

lemma sg31801 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,12,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9380

lemma sg31802 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,5,5,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10539

lemma sg31803 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,5,5,5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10540

lemma sg31804 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,5,5,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9424

lemma sg31805 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,5,5,5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10541

lemma sg31806 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,5,5,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9425

lemma sg31807 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10542

lemma sg31808 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10543

lemma sg31809 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9427

lemma sg31810 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5144 sg12699

lemma sg31811 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10380

lemma sg31812 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9423

lemma sg31813 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10544

lemma sg31814 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10545

lemma sg31815 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9428

lemma sg31816 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10541

lemma sg31817 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,5,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9429

lemma sg31818 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5158 sg12697

lemma sg31819 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8775 sg9594

lemma sg31820 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10538

lemma sg31821 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10546

lemma sg31822 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10547

lemma sg31823 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9430

lemma sg31824 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10469

lemma sg31825 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10383

lemma sg31826 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8885 sg9156

lemma sg31827 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10569

lemma sg31828 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9438

lemma sg31829 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10548

lemma sg31830 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9431

lemma sg31831 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10384

lemma sg31832 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8886 sg9156

lemma sg31833 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10549

lemma sg31834 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10549

lemma sg31835 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,6,6,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9432

lemma sg31836 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,7,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10550

lemma sg31837 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,8,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5162 sg12698

lemma sg31838 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,8,4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11361

lemma sg31839 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,8,4,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9434

lemma sg31840 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,8,4,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10554

lemma sg31841 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,8,4,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10555

lemma sg31842 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,10,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1728 sg18263

lemma sg31843 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,10,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2210 sg15583

lemma sg31844 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,10,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3903 sg14523

lemma sg31845 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,10,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7016 sg11478

lemma sg31846 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [13,10,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8836 sg9410

lemma sg31847 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,5,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10560

lemma sg31848 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,5,5,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10562

lemma sg31849 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,5,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5144 sg12700

lemma sg31850 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,5,5,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10448

lemma sg31851 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,5,5,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8827 sg9423

lemma sg31852 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,5,5,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10563

lemma sg31853 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,5,5,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10564

lemma sg31854 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,5,5,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9439

lemma sg31855 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10565

lemma sg31856 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5023 sg12702

lemma sg31857 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,5,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10465

lemma sg31858 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,5,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10559

lemma sg31859 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,5,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10566

lemma sg31860 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,5,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10567

lemma sg31861 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10523

lemma sg31862 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,5,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10467

lemma sg31863 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,5,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8491 sg10448

lemma sg31864 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,5,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10573

lemma sg31865 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5024 sg12702

lemma sg31866 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8779 sg9594

lemma sg31867 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10561

lemma sg31868 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10568

lemma sg31869 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10524

lemma sg31870 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10468

lemma sg31871 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8889 sg9156

lemma sg31872 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10574

lemma sg31873 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10469

lemma sg31874 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8508 sg10383

lemma sg31875 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,6,6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8508 sg10384

lemma sg31876 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,7,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5026 sg12702

lemma sg31877 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,7,4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10478

lemma sg31878 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,7,4,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9440

lemma sg31879 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,8,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5179 sg12698

lemma sg31880 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,8,4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10492

lemma sg31881 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,8,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10570

lemma sg31882 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,8,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10535

lemma sg31883 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,8,4,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10494

lemma sg31884 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,8,4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8491 sg10478

lemma sg31885 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,9,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1728 sg18272

lemma sg31886 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,9,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2498 sg15279

lemma sg31887 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,9,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5180 sg12698

lemma sg31888 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,9,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11362

lemma sg31889 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,9,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8836 sg9433

lemma sg31890 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,10,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1841 sg17144

lemma sg31891 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,10,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2211 sg15590

lemma sg31892 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,10,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2486 sg15292

lemma sg31893 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,10,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3904 sg14523

lemma sg31894 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,10,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4578 sg13503

lemma sg31895 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,10,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11363

lemma sg31896 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [14,10,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8172 sg11054

lemma sg31897 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [15,6,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5162 sg12700

lemma sg31898 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [15,6,4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10518

lemma sg31899 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [15,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1728 sg18273

lemma sg31900 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [15,8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2498 sg15280

lemma sg31901 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [15,8,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5039 sg12702

lemma sg31902 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [15,8,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10532

lemma sg31903 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5174 sg12700

lemma sg31904 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,5,4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10544

lemma sg31905 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5179 sg12700

lemma sg31906 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,6,4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10551

lemma sg31907 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,6,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10571

lemma sg31908 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1728 sg18274

lemma sg31909 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2498 sg15281

lemma sg31910 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5180 sg12700

lemma sg31911 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,7,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10553

lemma sg31912 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1841 sg17145

lemma sg31913 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,8,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2487 sg15293

lemma sg31914 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,8,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2498 sg15282

lemma sg31915 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,8,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5045 sg12702

lemma sg31916 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [16,8,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10572

lemma sg31917 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [17,4,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5187 sg12700

lemma sg31918 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [17,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1729 sg18274

lemma sg31919 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [17,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3752 sg14546

lemma sg31920 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [17,6,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5190 sg12700

lemma sg31921 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [18,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5195 sg12700

lemma sg31922 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [18,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1730 sg18274

lemma sg31923 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [18,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3753 sg14546

lemma sg31924 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [18,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5196 sg12700

lemma sg31925 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [18,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1842 sg17146

lemma sg31926 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [18,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3754 sg14546

lemma sg31927 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [18,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3752 sg14547

lemma sg31928 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [19,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1731 sg18274

lemma sg31929 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [19,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3755 sg14546

lemma sg31930 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [20,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1732 sg18274

lemma sg31931 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [20,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3756 sg14546

lemma sg31932 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [20,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1843 sg17146

lemma sg31933 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [21,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1733 sg18274

lemma sg31934 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [22,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1734 sg18274

lemma sg31935 : RowSquare [9,8,3,3,3,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2690 sg15690

lemma sg31936 : RowSquare [9,8,3,3,3,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2690 sg15691

lemma sg31937 : RowSquare [9,8,3,3,3,2,2,2,2,2,2,2,2,1,1] [7,6,6,6,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2247 sg20782

lemma sg31938 : RowSquare [9,8,3,3,3,2,2,2,2,2,2,2,2,1,1] [7,6,6,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2247 sg20783

lemma sg31939 : RowSquare [9,8,3,3,3,2,2,2,2,2,2,2,2,1,1] [7,7,6,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2691 sg15690

lemma sg31940 : RowSquare [9,8,3,3,3,2,2,2,2,2,2,2,2,1,1] [7,7,6,6,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2691 sg15691

lemma sg31941 : RowSquare [9,8,3,3,3,2,2,2,2,2,2,2,2,1,1] [7,7,7,6,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2692 sg15691

lemma sg31942 : RowSquare [9,8,4,3,2,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2665 sg15691

lemma sg31943 : RowSquare [9,9,3,3,2,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg21093

lemma sg31944 : RowSquare [9,9,3,3,2,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg21094

lemma sg31945 : RowSquare [9,9,3,3,2,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg21095

lemma sg31946 : RowSquare [9,9,3,3,2,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg21096

lemma sg31947 : RowSquare [9,9,3,3,2,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg21097

lemma sg31948 : RowSquare [9,9,3,3,2,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg21098

lemma sg31949 : RowSquare [9,9,3,3,2,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg21099

lemma sg31950 : RowSquare [9,9,3,3,2,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg21100

lemma sg31951 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg23531

lemma sg31952 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg23532

lemma sg31953 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12591 sg21202

lemma sg31954 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15255 sg15048

lemma sg31955 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15267 sg14997

lemma sg31956 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15283 sg14848

lemma sg31957 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14785 sg15559

lemma sg31958 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15267 sg14998

lemma sg31959 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15286 sg14814

lemma sg31960 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg15278 sg14978

lemma sg31961 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15290 sg14813

lemma sg31962 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15273 sg14980

lemma sg31963 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15267 sg14999

lemma sg31964 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15286 sg14815

lemma sg31965 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15158 sg15235

lemma sg31966 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15273 sg14981

lemma sg31967 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15272 sg14982

lemma sg31968 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15273 sg14982

lemma sg31969 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15247 sg15156

lemma sg31970 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,8,8,8,8,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12919 sg21084

lemma sg31971 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,8,8,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15247 sg15157

lemma sg31972 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15277 sg14979

lemma sg31973 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15274 sg14983

lemma sg31974 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15287 sg14816

lemma sg31975 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15275 sg14983

lemma sg31976 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15276 sg14983

lemma sg31977 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15288 sg14816

lemma sg31978 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg15289 sg14816

lemma sg31979 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15268 sg15000

lemma sg31980 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15269 sg15000

lemma sg31981 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15258 sg15005

lemma sg31982 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15270 sg14985

lemma sg31983 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15271 sg14985

lemma sg31984 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15254 sg15049

lemma sg31985 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15285 sg14818

lemma sg31986 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15254 sg15050

lemma sg31987 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,8,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15158 sg15236

lemma sg31988 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15267 sg15001

lemma sg31989 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15290 sg14814

lemma sg31990 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg15284 sg14848

lemma sg31991 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15267 sg15002

lemma sg31992 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15286 sg14817

lemma sg31993 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15291 sg14814

lemma sg31994 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15273 sg14984

lemma sg31995 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15286 sg14818

lemma sg31996 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15273 sg14985

lemma sg31997 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [11,9,9,9,9,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15158 sg15237

lemma sg31998 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [12,9,7,7,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15253 sg15051

lemma sg31999 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [13,8,7,7,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15253 sg15052

lemma sg32000 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [13,9,7,7,7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15253 sg15053

lemma sg32001 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [13,9,7,7,7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15259 sg15006

lemma sg32002 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [14,7,6,6,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15257 sg15007

lemma sg32003 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [14,7,7,6,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15257 sg15008

lemma sg32004 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [14,7,7,7,6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15257 sg15009

lemma sg32005 : RowSquare [14,12,6,5,4,3,2,2,2,2,2,2,1,1] [14,7,7,7,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15257 sg15010

lemma sg32007 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg11059 sg23530

lemma sg32008 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14310 sg21346

lemma sg32009 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5696 sg31942

lemma sg32010 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg31943

lemma sg32011 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14470 sg21297

lemma sg32012 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg31944

lemma sg32013 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15612 sg21051

lemma sg32014 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14471 sg21297

lemma sg32015 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17154

lemma sg32016 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,8,8,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17155

lemma sg32017 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17159

lemma sg32018 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15672 sg20946

lemma sg32019 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15102 sg21199

lemma sg32020 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17160

lemma sg32021 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17159

lemma sg32022 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17157

lemma sg32023 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17159

lemma sg32024 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17160

lemma sg32025 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17160

lemma sg32026 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16656

lemma sg32027 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,8,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg31945

lemma sg32028 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,8,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5731 sg31935

lemma sg32029 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,8,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg31946

lemma sg32030 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,8,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg31947

lemma sg32031 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,8,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17159

lemma sg32032 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,8,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17160

lemma sg32033 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,9,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg31948

lemma sg32034 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,9,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg31949

lemma sg32035 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,9,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5731 sg31936

lemma sg32036 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [9,9,9,9,9,9,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5670 sg31950

lemma sg32037 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14311 sg21345

lemma sg32038 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20430

lemma sg32039 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18116 sg20426

lemma sg32040 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15229 sg21188

lemma sg32041 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20431

lemma sg32042 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18116 sg20427

lemma sg32043 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20533 sg17152

lemma sg32044 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15224 sg21193

lemma sg32045 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17163

lemma sg32046 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,8,8,8,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17164

lemma sg32047 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17170

lemma sg32048 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20432

lemma sg32049 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20533 sg17153

lemma sg32050 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17177

lemma sg32051 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16227

lemma sg32052 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17177

lemma sg32053 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17170

lemma sg32054 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16227

lemma sg32055 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17149 sg20541

lemma sg32056 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16658

lemma sg32057 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,8,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12863 sg21635

lemma sg32058 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,8,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20433

lemma sg32059 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,8,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14724 sg21271

lemma sg32060 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,8,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15225 sg21193

lemma sg32061 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,8,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17170

lemma sg32062 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,8,8,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17171

lemma sg32063 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17278

lemma sg32064 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18295

lemma sg32065 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17278

lemma sg32066 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18295

lemma sg32067 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18281 sg20344

lemma sg32068 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18295

lemma sg32069 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg16649 sg20660

lemma sg32070 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18282 sg20344

lemma sg32071 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18295

lemma sg32072 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20554

lemma sg32073 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18295

lemma sg32074 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg16650 sg20660

lemma sg32075 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17213

lemma sg32076 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20794 sg16159

lemma sg32077 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16267

lemma sg32078 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16690

lemma sg32079 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17213

lemma sg32080 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20496 sg18104

lemma sg32081 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19575 sg19607

lemma sg32082 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17213

lemma sg32083 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20319 sg18293

lemma sg32084 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20320 sg18293

lemma sg32085 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17174

lemma sg32086 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20721 sg16219

lemma sg32087 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16659

lemma sg32088 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17174

lemma sg32089 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17174

lemma sg32090 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18288 sg20329

lemma sg32091 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17173

lemma sg32092 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20434

lemma sg32093 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20533 sg17156

lemma sg32094 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17175

lemma sg32095 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17173

lemma sg32096 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17172

lemma sg32097 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17175

lemma sg32098 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17175

lemma sg32099 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17176

lemma sg32100 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17176

lemma sg32101 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17176

lemma sg32102 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17174

lemma sg32103 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20644 sg16655

lemma sg32104 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20532 sg17158

lemma sg32105 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17175

lemma sg32106 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20435

lemma sg32107 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18116 sg20428

lemma sg32108 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17177

lemma sg32109 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17177

lemma sg32110 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17177

lemma sg32111 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17175

lemma sg32112 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17176

lemma sg32113 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17176

lemma sg32114 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16660

lemma sg32115 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17177

lemma sg32116 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20436

lemma sg32117 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20533 sg17157

lemma sg32118 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17177

lemma sg32119 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17177

lemma sg32120 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16661

lemma sg32121 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,8,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5731 sg31937

lemma sg32122 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,8,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6459 sg23673

lemma sg32123 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,8,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20533 sg17159

lemma sg32124 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,8,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17177

lemma sg32125 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,9,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5731 sg31938

lemma sg32126 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,9,9,9,9,9,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6459 sg23674

lemma sg32127 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12864 sg21634

lemma sg32128 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15248 sg21140

lemma sg32129 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14773 sg21251

lemma sg32130 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15231 sg21187

lemma sg32131 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20438

lemma sg32132 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17178

lemma sg32133 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15603 sg21076

lemma sg32134 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14764 sg21268

lemma sg32135 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17179

lemma sg32136 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,8,8,8,8,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17180

lemma sg32137 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17190

lemma sg32138 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20322 sg18290

lemma sg32139 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17190

lemma sg32140 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16670

end UniversalTensorSquare
end
end

end OAI
