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

/-! Semigroup Nodes 103. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg41741 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17727

lemma sg41742 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18241

lemma sg41743 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17901

lemma sg41744 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20092

lemma sg41745 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20092

lemma sg41746 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18820

lemma sg41747 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20092

lemma sg41748 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16968

lemma sg41749 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19470

lemma sg41750 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17794

lemma sg41751 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16081

lemma sg41752 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16969

lemma sg41753 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19471

lemma sg41754 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19105

lemma sg41755 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16928

lemma sg41756 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17746

lemma sg41757 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18094

lemma sg41758 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16929

lemma sg41759 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17731

lemma sg41760 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,7,7,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16930

lemma sg41761 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,4,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16574

lemma sg41762 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,4,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16082

lemma sg41763 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20689 sg16549

lemma sg41764 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20690 sg16549

lemma sg41765 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,4,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18821

lemma sg41766 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16970

lemma sg41767 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,4,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17795

lemma sg41768 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20093

lemma sg41769 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,4,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18821

lemma sg41770 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18822

lemma sg41771 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16034

lemma sg41772 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18823

lemma sg41773 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17902

lemma sg41774 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20094

lemma sg41775 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16083

lemma sg41776 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17747

lemma sg41777 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19858

lemma sg41778 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20094

lemma sg41779 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18822

lemma sg41780 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20094

lemma sg41781 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19472

lemma sg41782 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17903

lemma sg41783 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20095

lemma sg41784 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20095

lemma sg41785 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18823

lemma sg41786 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20095

lemma sg41787 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16971

lemma sg41788 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19473

lemma sg41789 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,5,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19106

lemma sg41790 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16632

lemma sg41791 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18824

lemma sg41792 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16972

lemma sg41793 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16575

lemma sg41794 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16036

lemma sg41795 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20709 sg16410

lemma sg41796 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20864 sg15858

lemma sg41797 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17904

lemma sg41798 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20096

lemma sg41799 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20096

lemma sg41800 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18824

lemma sg41801 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20096

lemma sg41802 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16972

lemma sg41803 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19474

lemma sg41804 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17797

lemma sg41805 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16084

lemma sg41806 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16973

lemma sg41807 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19475

lemma sg41808 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19107

lemma sg41809 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16815

lemma sg41810 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17751

lemma sg41811 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18095

lemma sg41812 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16816

lemma sg41813 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17905

lemma sg41814 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18825

lemma sg41815 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17905

lemma sg41816 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20097

lemma sg41817 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20097

lemma sg41818 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18825

lemma sg41819 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20097

lemma sg41820 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17798

lemma sg41821 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16085

lemma sg41822 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16974

lemma sg41823 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19476

lemma sg41824 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19108

lemma sg41825 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17753

lemma sg41826 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19109

lemma sg41827 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16817

lemma sg41828 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16414

lemma sg41829 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16818

lemma sg41830 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17731

lemma sg41831 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16975

lemma sg41832 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16576

lemma sg41833 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17799

lemma sg41834 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16086

lemma sg41835 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16975

lemma sg41836 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19477

lemma sg41837 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17754

lemma sg41838 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18096

lemma sg41839 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16819

lemma sg41840 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16416

lemma sg41841 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16820

lemma sg41842 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20536 sg17406

lemma sg41843 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,8,8,8,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17731

lemma sg41844 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,4,4,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20867 sg15846

lemma sg41845 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,4,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg16025

lemma sg41846 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,4,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20869 sg15846

lemma sg41847 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18828

lemma sg41848 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18826

lemma sg41849 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16040

lemma sg41850 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18826

lemma sg41851 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18283 sg20402

lemma sg41852 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16087

lemma sg41853 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20098

lemma sg41854 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18827

lemma sg41855 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17800

lemma sg41856 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,5,5,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18828

lemma sg41857 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,4,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16577

lemma sg41858 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,4,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18829

lemma sg41859 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,4,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg16026

lemma sg41860 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,4,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18829

lemma sg41861 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18831

lemma sg41862 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16088

lemma sg41863 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16577

lemma sg41864 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18830

lemma sg41865 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17801

lemma sg41866 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16578

lemma sg41867 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20099

lemma sg41868 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16089

lemma sg41869 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19869

lemma sg41870 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,5,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18831

lemma sg41871 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18832

lemma sg41872 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16042

lemma sg41873 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18833

lemma sg41874 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17906

lemma sg41875 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20100

lemma sg41876 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16090

lemma sg41877 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17757

lemma sg41878 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20100

lemma sg41879 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18832

lemma sg41880 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20100

lemma sg41881 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19478

lemma sg41882 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17907

lemma sg41883 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20101

lemma sg41884 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20101

lemma sg41885 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18833

lemma sg41886 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20101

lemma sg41887 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16976

lemma sg41888 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19479

lemma sg41889 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19110

lemma sg41890 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17802

lemma sg41891 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16091

lemma sg41892 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16977

lemma sg41893 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19480

lemma sg41894 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19111

lemma sg41895 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,6,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16931

lemma sg41896 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,4,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16579

lemma sg41897 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,4,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16092

lemma sg41898 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20689 sg16555

lemma sg41899 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20690 sg16555

lemma sg41900 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,4,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18834

lemma sg41901 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16978

lemma sg41902 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,4,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17803

lemma sg41903 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20102

lemma sg41904 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18835

lemma sg41905 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16044

lemma sg41906 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18836

lemma sg41907 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17908

lemma sg41908 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20103

lemma sg41909 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16093

lemma sg41910 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17760

lemma sg41911 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20103

lemma sg41912 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18835

lemma sg41913 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20103

lemma sg41914 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19481

lemma sg41915 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17909

lemma sg41916 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20104

lemma sg41917 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20104

lemma sg41918 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18836

lemma sg41919 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20104

lemma sg41920 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16979

lemma sg41921 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19482

lemma sg41922 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,5,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19112

lemma sg41923 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16633

lemma sg41924 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18837

lemma sg41925 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16980

lemma sg41926 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16580

lemma sg41927 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16047

lemma sg41928 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17740

lemma sg41929 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17910

lemma sg41930 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20105

lemma sg41931 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20105

lemma sg41932 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18837

lemma sg41933 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20105

lemma sg41934 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16980

lemma sg41935 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19483

lemma sg41936 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17805

lemma sg41937 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16094

lemma sg41938 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16981

lemma sg41939 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19484

lemma sg41940 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19113

lemma sg41941 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16932

lemma sg41942 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17763

lemma sg41943 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18097

lemma sg41944 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16933

lemma sg41945 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17911

lemma sg41946 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18838

lemma sg41947 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17911

lemma sg41948 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20106

lemma sg41949 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20106

lemma sg41950 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18838

lemma sg41951 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20106

lemma sg41952 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17806

lemma sg41953 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16095

lemma sg41954 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16982

lemma sg41955 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19485

lemma sg41956 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19114

lemma sg41957 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17765

lemma sg41958 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19115

lemma sg41959 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16934

lemma sg41960 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17746

lemma sg41961 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16935

lemma sg41962 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,7,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16409

lemma sg41963 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18839

lemma sg41964 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16050

lemma sg41965 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16582

lemma sg41966 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17912

lemma sg41967 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20107

lemma sg41968 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16096

lemma sg41969 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17766

lemma sg41970 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20107

lemma sg41971 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18839

lemma sg41972 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20107

lemma sg41973 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19486

lemma sg41974 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16634

lemma sg41975 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18840

lemma sg41976 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16983

lemma sg41977 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16581

lemma sg41978 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16051

lemma sg41979 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17747

lemma sg41980 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17913

lemma sg41981 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20108

lemma sg41982 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20108

lemma sg41983 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18840

lemma sg41984 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20108

lemma sg41985 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16983

lemma sg41986 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19487

lemma sg41987 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17808

lemma sg41988 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16097

lemma sg41989 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16984

lemma sg41990 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19488

lemma sg41991 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19116

lemma sg41992 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16936

lemma sg41993 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17914

lemma sg41994 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18841

lemma sg41995 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17914

lemma sg41996 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20109

lemma sg41997 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20109

lemma sg41998 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18841

lemma sg41999 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20109

lemma sg42000 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17809

lemma sg42001 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16098

lemma sg42002 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16985

lemma sg42003 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19489

lemma sg42004 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19117

lemma sg42005 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17769

lemma sg42006 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19118

lemma sg42007 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16937

lemma sg42008 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17751

lemma sg42009 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16938

lemma sg42010 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16986

lemma sg42011 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16583

lemma sg42012 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17810

lemma sg42013 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16099

lemma sg42014 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16986

lemma sg42015 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19490

lemma sg42016 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17770

lemma sg42017 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19119

lemma sg42018 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16939

lemma sg42019 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17753

lemma sg42020 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16940

lemma sg42021 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17746

lemma sg42022 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20719 sg16409

lemma sg42023 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,8,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17771

lemma sg42024 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,8,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16054

lemma sg42025 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,8,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17771

lemma sg42026 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,8,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18098

lemma sg42027 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,8,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17754

lemma sg42028 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,8,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16941

lemma sg42029 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,8,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20713 sg16416

lemma sg42030 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,8,8,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17746

lemma sg42031 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16584

lemma sg42032 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20863 sg15879

lemma sg42033 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16635

lemma sg42034 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18842

lemma sg42035 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16987

lemma sg42036 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16584

lemma sg42037 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16055

lemma sg42038 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20709 sg16428

lemma sg42039 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17915

lemma sg42040 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20110

lemma sg42041 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20110

lemma sg42042 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18842

lemma sg42043 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20110

lemma sg42044 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16987

lemma sg42045 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19491

lemma sg42046 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17916

lemma sg42047 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18843

lemma sg42048 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17916

lemma sg42049 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20111

lemma sg42050 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg20111

lemma sg42051 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18843

lemma sg42052 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg20111

lemma sg42053 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17812

lemma sg42054 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16100

lemma sg42055 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16988

lemma sg42056 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19492

lemma sg42057 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19120

lemma sg42058 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17773

lemma sg42059 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19121

lemma sg42060 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16833

lemma sg42061 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20631 sg16989

lemma sg42062 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16585

lemma sg42063 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17813

lemma sg42064 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16101

lemma sg42065 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16989

lemma sg42066 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19493

lemma sg42067 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17774

lemma sg42068 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19122

lemma sg42069 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16834

lemma sg42070 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16431

lemma sg42071 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16835

lemma sg42072 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,6,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17751

lemma sg42073 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17775

lemma sg42074 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16058

lemma sg42075 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17775

lemma sg42076 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19623 sg19123

lemma sg42077 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16432

lemma sg42078 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16836

lemma sg42079 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17753

lemma sg42080 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,7,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17751

lemma sg42081 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,8,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20709 sg16433

lemma sg42082 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,8,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20710 sg16433

lemma sg42083 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,8,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16837

lemma sg42084 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,8,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17754

lemma sg42085 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,8,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17753

lemma sg42086 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,9,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20837 sg16168

lemma sg42087 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,9,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20763 sg16314

lemma sg42088 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,10,9,9,9,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17754

lemma sg42089 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,5,5,5,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16102

lemma sg42090 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,5,5,5,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18844

lemma sg42091 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,5,5,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20840 sg16165

lemma sg42092 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,5,5,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16059

lemma sg42093 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,5,5,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16103

lemma sg42094 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,5,5,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18283 sg20403

lemma sg42095 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,5,5,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18845

lemma sg42096 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,5,5,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18846

lemma sg42097 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,4,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20863 sg15884

lemma sg42098 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,5,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16060

lemma sg42099 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,5,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16586

lemma sg42100 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,5,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18847

lemma sg42101 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,5,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16104

lemma sg42102 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,5,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20690 sg16564

lemma sg42103 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,5,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18848

lemma sg42104 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18851

lemma sg42105 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18849

lemma sg42106 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16061

lemma sg42107 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18852

lemma sg42108 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16105

lemma sg42109 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20112

lemma sg42110 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18850

lemma sg42111 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18851

lemma sg42112 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20708 sg16441

lemma sg42113 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20113

lemma sg42114 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16106

lemma sg42115 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18852

lemma sg42116 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,6,6,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18099

lemma sg42117 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,5,4,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg16059

lemma sg42118 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,5,5,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16064

lemma sg42119 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,5,5,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18283 sg20404

lemma sg42120 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,5,5,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18853

lemma sg42121 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,5,5,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16107

lemma sg42122 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,5,5,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20854 sg16063

lemma sg42123 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,5,5,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18854

lemma sg42124 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,4,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg16060

lemma sg42125 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,5,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18857

lemma sg42126 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,5,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18855

lemma sg42127 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,5,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg16065

lemma sg42128 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,5,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16588

lemma sg42129 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,5,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16108

lemma sg42130 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,5,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20114

lemma sg42131 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,5,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18856

lemma sg42132 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,5,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18857

lemma sg42133 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18859

lemma sg42134 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16109

lemma sg42135 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16587

lemma sg42136 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18858

lemma sg42137 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18860

lemma sg42138 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg20115

lemma sg42139 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16110

lemma sg42140 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,7,6,6,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18859

end UniversalTensorSquare
end
end

end OAI
