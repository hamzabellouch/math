import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes13
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes11
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes9

namespace OAI

/-! Semigroup Nodes 33. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13740 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2393 sg2803

lemma sg13741 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2318 sg3005

lemma sg13742 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2341 sg2928

lemma sg13743 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3027

lemma sg13744 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3027

lemma sg13745 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg636 sg5790

lemma sg13746 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3028

lemma sg13747 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3028

lemma sg13748 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2405 sg2773

lemma sg13749 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,2] := by
  exact rowSquare_join (by decide) sg2406 sg2772

lemma sg13750 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1] := by
  exact rowSquare_join (by decide) sg2407 sg2772

lemma sg13751 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1323 sg4526

lemma sg13752 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2433 sg2763

lemma sg13753 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg2318 sg3008

lemma sg13754 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg2406 sg2773

lemma sg13755 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4] := by
  exact rowSquare_join (by decide) sg2407 sg2773

lemma sg13756 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg1848 sg3703

lemma sg13757 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,1] := by
  exact rowSquare_join (by decide) sg2395 sg2806

lemma sg13758 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3] := by
  exact rowSquare_join (by decide) sg2395 sg2807

lemma sg13759 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1921 sg3632

lemma sg13760 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2403 sg2798

lemma sg13761 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2352 sg2925

lemma sg13762 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3119

lemma sg13763 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2310 sg3029

lemma sg13764 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2345 sg2926

lemma sg13765 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2353 sg2925

lemma sg13766 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1803 sg3724

lemma sg13767 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2312 sg3010

lemma sg13768 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1803 sg3725

lemma sg13769 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2310 sg3030

lemma sg13770 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2312 sg3012

lemma sg13771 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg3030

lemma sg13772 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1803 sg3726

lemma sg13773 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3031

lemma sg13774 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2809

lemma sg13775 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3031

lemma sg13776 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2339 sg2930

lemma sg13777 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2810

lemma sg13778 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2310 sg3032

lemma sg13779 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2346 sg2926

lemma sg13780 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2355 sg2925

lemma sg13781 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3120

lemma sg13782 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2312 sg3013

lemma sg13783 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3121

lemma sg13784 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2310 sg3033

lemma sg13785 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2315 sg3012

lemma sg13786 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg3033

lemma sg13787 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg4536

lemma sg13788 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2312 sg3014

lemma sg13789 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg4537

lemma sg13790 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3034

lemma sg13791 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2811

lemma sg13792 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3034

lemma sg13793 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3035

lemma sg13794 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3035

lemma sg13795 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2339 sg2931

lemma sg13796 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3122

lemma sg13797 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2320 sg3005

lemma sg13798 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg4538

lemma sg13799 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2312 sg3016

lemma sg13800 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3123

lemma sg13801 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3036

lemma sg13802 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2812

lemma sg13803 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3036

lemma sg13804 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3124

lemma sg13805 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2312 sg3017

lemma sg13806 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2409 sg2771

lemma sg13807 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3037

lemma sg13808 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3037

lemma sg13809 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2932

lemma sg13810 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2813

lemma sg13811 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg2339 sg2933

lemma sg13812 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg4539

lemma sg13813 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3038

lemma sg13814 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3038

lemma sg13815 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2814

lemma sg13816 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg2339 sg2934

lemma sg13817 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg2396 sg2807

lemma sg13818 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5] := by
  exact rowSquare_join (by decide) sg1956 sg3505

lemma sg13819 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2810

lemma sg13820 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2312 sg3020

lemma sg13821 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2392 sg2810

lemma sg13822 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2310 sg3039

lemma sg13823 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2321 sg3004

lemma sg13824 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg3039

lemma sg13825 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2393 sg2810

lemma sg13826 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2315 sg3013

lemma sg13827 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3125

lemma sg13828 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2312 sg3021

lemma sg13829 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2394 sg2810

lemma sg13830 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3040

lemma sg13831 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2816

lemma sg13832 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3040

lemma sg13833 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2395 sg2810

lemma sg13834 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2312 sg3022

lemma sg13835 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2391 sg2811

lemma sg13836 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3041

lemma sg13837 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3041

lemma sg13838 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2936

lemma sg13839 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2817

lemma sg13840 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2339 sg2937

lemma sg13841 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3126

lemma sg13842 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2315 sg3016

lemma sg13843 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3127

lemma sg13844 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2312 sg3024

lemma sg13845 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2391 sg2812

lemma sg13846 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3042

lemma sg13847 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3042

lemma sg13848 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2938

lemma sg13849 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3128

lemma sg13850 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3043

lemma sg13851 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3043

lemma sg13852 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2819

lemma sg13853 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg2339 sg2939

lemma sg13854 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg2340 sg2933

lemma sg13855 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2312 sg3026

lemma sg13856 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2820

lemma sg13857 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2339 sg2940

lemma sg13858 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg2340 sg2934

lemma sg13859 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4] := by
  exact rowSquare_join (by decide) sg2413 sg2773

lemma sg13860 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3130

lemma sg13861 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2439 sg2763

lemma sg13862 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,2,1] := by
  exact rowSquare_join (by decide) sg2342 sg2934

lemma sg13863 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3] := by
  exact rowSquare_join (by decide) sg2432 sg2764

lemma sg13864 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,1,1] := by
  exact rowSquare_join (by decide) sg2398 sg2806

lemma sg13865 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2] := by
  exact rowSquare_join (by decide) sg2433 sg2764

lemma sg13866 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1961 sg3503

lemma sg13867 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2315 sg3020

lemma sg13868 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1963 sg3503

lemma sg13869 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2391 sg2815

lemma sg13870 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3044

lemma sg13871 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2350 sg2927

lemma sg13872 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3044

lemma sg13873 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2315 sg3021

lemma sg13874 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2315 sg3022

lemma sg13875 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2391 sg2816

lemma sg13876 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3045

lemma sg13877 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3045

lemma sg13878 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2400 sg2802

lemma sg13879 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3046

lemma sg13880 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3046

lemma sg13881 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2817

lemma sg13882 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2340 sg2936

lemma sg13883 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2340 sg2937

lemma sg13884 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3047

lemma sg13885 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,3,2] := by
  exact rowSquare_join (by decide) sg2340 sg2938

lemma sg13886 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2315 sg3026

lemma sg13887 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2819

lemma sg13888 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,2,2] := by
  exact rowSquare_join (by decide) sg2342 sg2936

lemma sg13889 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,3,1] := by
  exact rowSquare_join (by decide) sg2340 sg2939

lemma sg13890 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4] := by
  exact rowSquare_join (by decide) sg2432 sg2766

lemma sg13891 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2820

lemma sg13892 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,1] := by
  exact rowSquare_join (by decide) sg2340 sg2940

lemma sg13893 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3] := by
  exact rowSquare_join (by decide) sg2433 sg2766

lemma sg13894 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2822

lemma sg13895 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,1,1] := by
  exact rowSquare_join (by decide) sg2342 sg2940

lemma sg13896 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2] := by
  exact rowSquare_join (by decide) sg2432 sg2767

lemma sg13897 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,1] := by
  exact rowSquare_join (by decide) sg2433 sg2767

lemma sg13898 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6] := by
  exact rowSquare_join (by decide) sg1848 sg3712

lemma sg13899 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2326 sg3001

lemma sg13900 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2404 sg2798

lemma sg13901 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2356 sg2925

lemma sg13902 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2186 sg3119

lemma sg13903 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2310 sg3049

lemma sg13904 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2326 sg3004

lemma sg13905 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2352 sg2926

lemma sg13906 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2357 sg2925

lemma sg13907 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3131

lemma sg13908 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2312 sg3029

lemma sg13909 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3132

lemma sg13910 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2310 sg3050

lemma sg13911 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2345 sg2930

lemma sg13912 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg3050

lemma sg13913 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2326 sg3008

lemma sg13914 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2312 sg3030

lemma sg13915 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2326 sg3009

lemma sg13916 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3051

lemma sg13917 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2824

lemma sg13918 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3051

lemma sg13919 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3052

lemma sg13920 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3052

lemma sg13921 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2339 sg2943

lemma sg13922 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2186 sg3120

lemma sg13923 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2312 sg3032

lemma sg13924 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2186 sg3121

lemma sg13925 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2310 sg3053

lemma sg13926 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2346 sg2930

lemma sg13927 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg3053

lemma sg13928 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3133

lemma sg13929 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2315 sg3029

lemma sg13930 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3134

lemma sg13931 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2312 sg3033

lemma sg13932 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3135

lemma sg13933 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg3054

lemma sg13934 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2825

lemma sg13935 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3054

lemma sg13936 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2186 sg3124

lemma sg13937 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2312 sg3034

lemma sg13938 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2391 sg2824

lemma sg13939 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3055

lemma sg13940 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2944

lemma sg13941 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2826

lemma sg13942 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2339 sg2945

lemma sg13943 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3136

lemma sg13944 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3137

lemma sg13945 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3056

lemma sg13946 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2946

lemma sg13947 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3138

lemma sg13948 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg2339 sg2947

lemma sg13949 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2827

lemma sg13950 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3139

lemma sg13951 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2186 sg3125

lemma sg13952 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2169 sg3149

lemma sg13953 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2828

lemma sg13954 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3057

lemma sg13955 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3140

lemma sg13956 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3141

lemma sg13957 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2948

lemma sg13958 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2186 sg3128

lemma sg13959 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2339 sg2949

lemma sg13960 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3142

lemma sg13961 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3143

lemma sg13962 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2829

lemma sg13963 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2827

lemma sg13964 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2401 sg2810

lemma sg13965 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2951

lemma sg13966 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,2] := by
  exact rowSquare_join (by decide) sg2339 sg2952

lemma sg13967 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2830

lemma sg13968 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2339 sg2953

lemma sg13969 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2340 sg2949

lemma sg13970 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4] := by
  exact rowSquare_join (by decide) sg2436 sg2766

lemma sg13971 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2829

lemma sg13972 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,1] := by
  exact rowSquare_join (by decide) sg2340 sg2950

lemma sg13973 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3] := by
  exact rowSquare_join (by decide) sg2432 sg2768

lemma sg13974 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,1,1] := by
  exact rowSquare_join (by decide) sg2435 sg2767

lemma sg13975 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2] := by
  exact rowSquare_join (by decide) sg2436 sg2767

lemma sg13976 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1961 sg3508

lemma sg13977 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1962 sg3508

lemma sg13978 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2350 sg2935

lemma sg13979 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1963 sg3508

lemma sg13980 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3058

lemma sg13981 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2350 sg2937

lemma sg13982 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2340 sg2951

lemma sg13983 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2326 sg3012

lemma sg13984 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2358 sg2925

lemma sg13985 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2186 sg3132

lemma sg13986 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg3059

lemma sg13987 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3145

lemma sg13988 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg3146

lemma sg13989 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2832

lemma sg13990 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3060

lemma sg13991 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2326 sg3019

lemma sg13992 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2954

lemma sg13993 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2833

lemma sg13994 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2834

lemma sg13995 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3061

lemma sg13996 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3062

lemma sg13997 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2955

lemma sg13998 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3063

lemma sg13999 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2339 sg2956

lemma sg14000 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2390 sg2835

lemma sg14001 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3064

lemma sg14002 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2350 sg2952

lemma sg14003 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2391 sg2835

lemma sg14004 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3] := by
  exact rowSquare_join (by decide) sg2479 sg2657

lemma sg14005 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg3065

lemma sg14006 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2836

lemma sg14007 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg3066

lemma sg14008 : RowSquare [4,4,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2311 sg3067

lemma sg14009 : RowSquare [4,4,3,3,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg3505

lemma sg14010 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2311 sg2925

lemma sg14011 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2313 sg2925

lemma sg14012 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2311 sg2926

lemma sg14013 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg4976

lemma sg14014 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2311 sg2930

lemma sg14015 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2322 sg2925

lemma sg14016 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg1032 sg4977

lemma sg14017 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg1033 sg4977

lemma sg14018 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2324 sg2925

lemma sg14019 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1033 sg4978

lemma sg14020 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1032 sg4979

lemma sg14021 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1032 sg4980

lemma sg14022 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,5] := by
  exact rowSquare_join (by decide) sg1033 sg4980

lemma sg14023 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2314 sg2930

lemma sg14024 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2327 sg2925

lemma sg14025 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2399 sg2761

lemma sg14026 : RowSquare [4,4,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2311 sg2951

lemma sg14027 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg4927

lemma sg14028 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2209 sg2925

lemma sg14029 : RowSquare [4,4,4,3,2,2,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2390 sg2661

lemma sg14030 : RowSquare [4,4,4,3,3,2,1,1,1,1,1,1,1] [6,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2149 sg2925

lemma sg14031 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg976 sg4997

lemma sg14032 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3069

lemma sg14033 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1844 sg3690

lemma sg14034 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1844 sg3691

lemma sg14035 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2348 sg2902

lemma sg14036 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg2339 sg2907

lemma sg14037 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3073

lemma sg14038 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg1844 sg3694

lemma sg14039 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2370 sg2837

lemma sg14040 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2212 sg3117

lemma sg14041 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1844 sg3697

lemma sg14042 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3077

lemma sg14043 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2371 sg2840

lemma sg14044 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg975 sg4998

lemma sg14045 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg2373 sg2838

lemma sg14046 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3078

lemma sg14047 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2330 sg2959

lemma sg14048 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg3069

lemma sg14049 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg2329 sg2961

lemma sg14050 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg2340 sg2908

lemma sg14051 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5] := by
  exact rowSquare_join (by decide) sg1916 sg3622

lemma sg14052 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg3660

lemma sg14053 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2372 sg2839

lemma sg14054 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3079

lemma sg14055 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2373 sg2839

lemma sg14056 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg975 sg4999

lemma sg14057 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2374 sg2839

lemma sg14058 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg2341 sg2907

lemma sg14059 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg1844 sg3699

lemma sg14060 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3080

lemma sg14061 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2372 sg2840

lemma sg14062 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2341 sg2908

lemma sg14063 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,2] := by
  exact rowSquare_join (by decide) sg2342 sg2907

lemma sg14064 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1] := by
  exact rowSquare_join (by decide) sg2432 sg2747

lemma sg14065 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2330 sg2960

lemma sg14066 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg2373 sg2840

lemma sg14067 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg2342 sg2908

lemma sg14068 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4] := by
  exact rowSquare_join (by decide) sg2432 sg2749

lemma sg14069 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,1] := by
  exact rowSquare_join (by decide) sg2433 sg2748

lemma sg14070 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3] := by
  exact rowSquare_join (by decide) sg2433 sg2749

lemma sg14071 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2213 sg3110

lemma sg14072 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2354 sg2902

lemma sg14073 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2213 sg3111

lemma sg14074 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3083

lemma sg14075 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2216 sg3111

lemma sg14076 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3087

lemma sg14077 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2153 sg3155

lemma sg14078 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2213 sg3118

lemma sg14079 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2153 sg3156

lemma sg14080 : RowSquare [5,3,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2216 sg3118

lemma sg14081 : RowSquare [5,3,3,3,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1688 sg3732

lemma sg14082 : RowSquare [5,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3011

lemma sg14083 : RowSquare [5,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg3012

lemma sg14084 : RowSquare [5,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1910 sg3614

lemma sg14085 : RowSquare [5,4,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg1926 sg3565

lemma sg14086 : RowSquare [5,4,3,2,2,2,2,2,2,2,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1871 sg3299

lemma sg14087 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg3476

lemma sg14088 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1688 sg3726

lemma sg14089 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg872 sg4965

lemma sg14090 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1239 sg4439

lemma sg14091 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg872 sg4966

lemma sg14092 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1699 sg3614

lemma sg14093 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg873 sg4966

lemma sg14094 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2147 sg2902

lemma sg14095 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2310 sg2646

lemma sg14096 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1700 sg3614

lemma sg14097 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg2310 sg2647

lemma sg14098 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2311 sg2647

lemma sg14099 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2140 sg3004

lemma sg14100 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2141 sg3003

lemma sg14101 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2141 sg3004

lemma sg14102 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [5,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1688 sg3648

lemma sg14103 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1701 sg3614

lemma sg14104 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg876 sg4966

lemma sg14105 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2148 sg2902

lemma sg14106 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2310 sg2651

lemma sg14107 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg2311 sg2650

lemma sg14108 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg2311 sg2651

lemma sg14109 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [6,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2144 sg3004

lemma sg14110 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [6,6,5,5,5] := by
  exact rowSquare_join (by decide) sg1916 sg3337

lemma sg14111 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [7,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2150 sg2902

lemma sg14112 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [7,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2314 sg2651

lemma sg14113 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [7,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2213 sg2718

lemma sg14114 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [7,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2216 sg2718

lemma sg14115 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [7,7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2138 sg3044

lemma sg14116 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [8,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2139 sg3048

lemma sg14117 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [8,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2213 sg2719

lemma sg14118 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [8,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2216 sg2719

lemma sg14119 : RowSquare [5,4,3,3,3,2,1,1,1,1,1,1,1] [8,8,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2138 sg3058

lemma sg14120 : RowSquare [5,4,4,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1682 sg3632

lemma sg14121 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2288 sg2957

lemma sg14122 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2288 sg2958

lemma sg14123 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1874 sg3650

lemma sg14124 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2962

lemma sg14125 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2288 sg2963

lemma sg14126 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2288 sg2965

lemma sg14127 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2289 sg2958

lemma sg14128 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2291 sg2958

lemma sg14129 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2294 sg2958

lemma sg14130 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2296 sg2958

lemma sg14131 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2977

lemma sg14132 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2297 sg2959

lemma sg14133 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg2293 sg2961

lemma sg14134 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg2293 sg2962

lemma sg14135 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1874 sg3652

lemma sg14136 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2288 sg2978

lemma sg14137 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg2372 sg2783

lemma sg14138 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2372 sg2784

lemma sg14139 : RowSquare [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg2297 sg2960

end UniversalTensorSquare
end
end

end OAI
