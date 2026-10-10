import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 63. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25740 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9025

lemma sg25741 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg8543 sg10099

lemma sg25742 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8179 sg10859

lemma sg25743 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg8543 sg10100

lemma sg25744 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg8571 sg10086

lemma sg25745 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9795

lemma sg25746 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8345 sg10690

lemma sg25747 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9825

lemma sg25748 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9543

lemma sg25749 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10374

lemma sg25750 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10691

lemma sg25751 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9826

lemma sg25752 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9476

lemma sg25753 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10375

lemma sg25754 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10299

lemma sg25755 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9827

lemma sg25756 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8347 sg10669

lemma sg25757 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10376

lemma sg25758 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10300

lemma sg25759 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9828

lemma sg25760 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9798

lemma sg25761 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10275

lemma sg25762 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9090

lemma sg25763 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9799

lemma sg25764 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10276

lemma sg25765 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10268

lemma sg25766 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9091

lemma sg25767 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8862 sg9019

lemma sg25768 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9543

lemma sg25769 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10377

lemma sg25770 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10301

lemma sg25771 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9829

lemma sg25772 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8347 sg10672

lemma sg25773 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9543

lemma sg25774 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10378

lemma sg25775 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10302

lemma sg25776 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9830

lemma sg25777 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9801

lemma sg25778 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10277

lemma sg25779 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9092

lemma sg25780 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10303

lemma sg25781 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9831

lemma sg25782 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9802

lemma sg25783 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10278

lemma sg25784 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10271

lemma sg25785 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9093

lemma sg25786 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9544

lemma sg25787 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10272

lemma sg25788 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9094

lemma sg25789 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10663

lemma sg25790 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10379

lemma sg25791 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10304

lemma sg25792 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9832

lemma sg25793 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9803

lemma sg25794 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10279

lemma sg25795 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10273

lemma sg25796 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9095

lemma sg25797 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9804

lemma sg25798 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10280

lemma sg25799 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9545

lemma sg25800 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10274

lemma sg25801 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9096

lemma sg25802 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg9023

lemma sg25803 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9479

lemma sg25804 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9024

lemma sg25805 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8526 sg10130

lemma sg25806 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10104

lemma sg25807 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9097

lemma sg25808 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10102

lemma sg25809 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9025

lemma sg25810 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg8864 sg9016

lemma sg25811 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15514

lemma sg25812 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3887 sg14500

lemma sg25813 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3872 sg14508

lemma sg25814 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5564 sg12618

lemma sg25815 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5986 sg11829

lemma sg25816 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9194

lemma sg25817 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9243

lemma sg25818 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9477

lemma sg25819 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3163 sg14802

lemma sg25820 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6941 sg11468

lemma sg25821 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5987 sg11829

lemma sg25822 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9215

lemma sg25823 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9194

lemma sg25824 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9789

lemma sg25825 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9477

lemma sg25826 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6917 sg11474

lemma sg25827 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10380

lemma sg25828 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9215

lemma sg25829 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10709

lemma sg25830 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10380

lemma sg25831 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10305

lemma sg25832 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9833

lemma sg25833 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10305

lemma sg25834 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9833

lemma sg25835 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9805

lemma sg25836 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10677

lemma sg25837 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8861 sg9034

lemma sg25838 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6942 sg11468

lemma sg25839 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6918 sg11474

lemma sg25840 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10381

lemma sg25841 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9195

lemma sg25842 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10710

lemma sg25843 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10381

lemma sg25844 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10306

lemma sg25845 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10306

lemma sg25846 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9834

lemma sg25847 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10306

lemma sg25848 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9834

lemma sg25849 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9806

lemma sg25850 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9806

lemma sg25851 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10281

lemma sg25852 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9195

lemma sg25853 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8861 sg9035

lemma sg25854 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9217

lemma sg25855 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9807

lemma sg25856 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9807

lemma sg25857 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10282

lemma sg25858 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9196

lemma sg25859 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9196

lemma sg25860 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9036

lemma sg25861 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10664

lemma sg25862 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10272

lemma sg25863 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10665

lemma sg25864 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6919 sg11474

lemma sg25865 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10307

lemma sg25866 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10307

lemma sg25867 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9835

lemma sg25868 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10307

lemma sg25869 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9835

lemma sg25870 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9218

lemma sg25871 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9808

lemma sg25872 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9808

lemma sg25873 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10283

lemma sg25874 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9197

lemma sg25875 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9197

lemma sg25876 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9037

lemma sg25877 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10666

lemma sg25878 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8726 sg9492

lemma sg25879 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9492

lemma sg25880 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9492

lemma sg25881 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9038

lemma sg25882 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10274

lemma sg25883 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10667

lemma sg25884 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10272

lemma sg25885 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8527 sg10130

lemma sg25886 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8563 sg10098

lemma sg25887 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg8564 sg10098

lemma sg25888 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg8863 sg9025

lemma sg25889 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10284

lemma sg25890 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10230

lemma sg25891 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9809

lemma sg25892 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9809

lemma sg25893 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10284

lemma sg25894 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8726 sg9493

lemma sg25895 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9493

lemma sg25896 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9493

lemma sg25897 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9039

lemma sg25898 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8754 sg9468

lemma sg25899 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8876 sg9002

lemma sg25900 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8477 sg10195

lemma sg25901 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8478 sg10195

lemma sg25902 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8479 sg10195

lemma sg25903 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10274

lemma sg25904 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8484 sg10182

lemma sg25905 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg8352 sg10667

lemma sg25906 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1321 sg20962

lemma sg25907 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1724 sg18243

lemma sg25908 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1825 sg17109

lemma sg25909 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2191 sg15563

lemma sg25910 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15529

lemma sg25911 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2228 sg15521

lemma sg25912 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg15572

lemma sg25913 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3517 sg14680

lemma sg25914 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg867 sg21141

lemma sg25915 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg867 sg21142

lemma sg25916 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg867 sg21143

lemma sg25917 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1826 sg17109

lemma sg25918 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2192 sg15563

lemma sg25919 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2225 sg15529

lemma sg25920 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2670 sg15016

lemma sg25921 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2872 sg14852

lemma sg25922 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5591 sg12609

lemma sg25923 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3513 sg14683

lemma sg25924 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5626 sg12603

lemma sg25925 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5591 sg12610

lemma sg25926 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2226 sg15529

lemma sg25927 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2671 sg15016

lemma sg25928 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15530

lemma sg25929 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5261 sg12683

lemma sg25930 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg15573

lemma sg25931 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9186

lemma sg25932 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5624 sg12604

lemma sg25933 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8729 sg9480

lemma sg25934 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2177 sg15572

lemma sg25935 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6937 sg11469

lemma sg25936 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5241 sg12691

lemma sg25937 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9187

lemma sg25938 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8833 sg9166

lemma sg25939 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8651 sg9795

lemma sg25940 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6914 sg11475

lemma sg25941 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9188

lemma sg25942 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8877 sg8995

lemma sg25943 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9689

lemma sg25944 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9546

lemma sg25945 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8480 sg10190

lemma sg25946 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9690

lemma sg25947 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8529 sg10116

lemma sg25948 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10133

lemma sg25949 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8530 sg10116

lemma sg25950 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2193 sg15563

lemma sg25951 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2227 sg15529

lemma sg25952 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2672 sg15016

lemma sg25953 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14853

lemma sg25954 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5250 sg12689

lemma sg25955 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2666 sg15021

lemma sg25956 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9189

lemma sg25957 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5625 sg12604

lemma sg25958 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8732 sg9480

lemma sg25959 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14506

lemma sg25960 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2671 sg15017

lemma sg25961 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6938 sg11469

lemma sg25962 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5965 sg11832

lemma sg25963 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9219

lemma sg25964 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9248

lemma sg25965 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8652 sg9795

lemma sg25966 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6939 sg11469

lemma sg25967 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6915 sg11475

lemma sg25968 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10275

lemma sg25969 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9219

lemma sg25970 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9796

lemma sg25971 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9546

lemma sg25972 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10276

lemma sg25973 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9188

lemma sg25974 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10711

lemma sg25975 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8720 sg9547

lemma sg25976 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9836

lemma sg25977 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10134

lemma sg25978 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9836

lemma sg25979 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9219

lemma sg25980 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14507

lemma sg25981 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6940 sg11469

lemma sg25982 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6916 sg11475

lemma sg25983 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9193

lemma sg25984 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9249

lemma sg25985 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9186

lemma sg25986 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9546

lemma sg25987 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5990 sg11828

lemma sg25988 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9220

lemma sg25989 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9250

lemma sg25990 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10712

lemma sg25991 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8808 sg9186

lemma sg25992 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9251

lemma sg25993 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9837

lemma sg25994 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10695

lemma sg25995 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9837

lemma sg25996 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8724 sg9520

lemma sg25997 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8725 sg9520

lemma sg25998 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9098

lemma sg25999 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8255 sg10846

lemma sg26000 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9220

lemma sg26001 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9838

lemma sg26002 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10135

lemma sg26003 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9838

lemma sg26004 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9220

lemma sg26005 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9220

lemma sg26006 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9220

lemma sg26007 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10275

lemma sg26008 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9099

lemma sg26009 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9548

lemma sg26010 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10276

lemma sg26011 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9100

lemma sg26012 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg9027

lemma sg26013 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15515

lemma sg26014 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14506

lemma sg26015 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2870 sg14853

lemma sg26016 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5548 sg12626

lemma sg26017 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5989 sg11829

lemma sg26018 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9194

lemma sg26019 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9248

lemma sg26020 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9481

lemma sg26021 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14508

lemma sg26022 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6941 sg11469

lemma sg26023 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5967 sg11832

lemma sg26024 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10277

lemma sg26025 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9252

lemma sg26026 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9796

lemma sg26027 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9481

lemma sg26028 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6917 sg11475

lemma sg26029 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10278

lemma sg26030 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9250

lemma sg26031 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10713

lemma sg26032 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9547

lemma sg26033 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9251

lemma sg26034 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9839

lemma sg26035 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10696

lemma sg26036 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9839

lemma sg26037 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8724 sg9522

lemma sg26038 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8725 sg9522

lemma sg26039 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9101

lemma sg26040 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6942 sg11469

lemma sg26041 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6918 sg11475

lemma sg26042 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10382

lemma sg26043 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9253

lemma sg26044 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10714

lemma sg26045 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10382

lemma sg26046 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9222

lemma sg26047 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9221

lemma sg26048 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9840

lemma sg26049 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10697

lemma sg26050 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9840

lemma sg26051 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9221

lemma sg26052 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9221

lemma sg26053 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9221

lemma sg26054 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10277

lemma sg26055 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9102

lemma sg26056 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9222

lemma sg26057 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9222

lemma sg26058 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9222

lemma sg26059 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9222

lemma sg26060 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9549

lemma sg26061 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10278

lemma sg26062 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9103

lemma sg26063 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10670

lemma sg26064 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10276

lemma sg26065 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10671

lemma sg26066 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6919 sg11475

lemma sg26067 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9223

lemma sg26068 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9255

lemma sg26069 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9841

lemma sg26070 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10698

lemma sg26071 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9841

lemma sg26072 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9223

lemma sg26073 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9223

lemma sg26074 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9223

lemma sg26075 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9223

lemma sg26076 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9550

lemma sg26077 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10279

lemma sg26078 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9104

lemma sg26079 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg9031

lemma sg26080 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9804

lemma sg26081 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9551

lemma sg26082 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10280

lemma sg26083 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9105

lemma sg26084 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9488

lemma sg26085 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9032

lemma sg26086 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10276

lemma sg26087 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8534 sg10104

lemma sg26088 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10104

lemma sg26089 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9033

lemma sg26090 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg8879 sg8998

lemma sg26091 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14506

lemma sg26092 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14508

lemma sg26093 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5551 sg12626

lemma sg26094 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5991 sg11829

lemma sg26095 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8601 sg10081

lemma sg26096 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9252

lemma sg26097 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9189

lemma sg26098 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8756 sg9459

lemma sg26099 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5552 sg12626

lemma sg26100 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5970 sg11832

lemma sg26101 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10383

lemma sg26102 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9256

lemma sg26103 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10715

lemma sg26104 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10383

lemma sg26105 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10282

lemma sg26106 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9224

lemma sg26107 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9842

lemma sg26108 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10699

lemma sg26109 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9842

lemma sg26110 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9224

lemma sg26111 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9224

lemma sg26112 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9224

lemma sg26113 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8823 sg9178

lemma sg26114 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9106

lemma sg26115 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5971 sg11832

lemma sg26116 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9225

lemma sg26117 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9257

lemma sg26118 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9843

lemma sg26119 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10700

lemma sg26120 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9843

lemma sg26121 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9225

lemma sg26122 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9225

lemma sg26123 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9225

lemma sg26124 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9225

lemma sg26125 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9552

lemma sg26126 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10281

lemma sg26127 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9107

lemma sg26128 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10673

lemma sg26129 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9807

lemma sg26130 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9553

lemma sg26131 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10282

lemma sg26132 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9108

lemma sg26133 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10278

lemma sg26134 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10674

lemma sg26135 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8863 sg9030

lemma sg26136 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9226

lemma sg26137 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9226

lemma sg26138 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9226

lemma sg26139 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9226

end UniversalTensorSquare
end
end

end OAI
