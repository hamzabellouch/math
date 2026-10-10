import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 73. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29740 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9258

lemma sg29741 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10349

lemma sg29742 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10360

lemma sg29743 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9282

lemma sg29744 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9919

lemma sg29745 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9919

lemma sg29746 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10360

lemma sg29747 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9259

lemma sg29748 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9259

lemma sg29749 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9259

lemma sg29750 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10350

lemma sg29751 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9605

lemma sg29752 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10351

lemma sg29753 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9260

lemma sg29754 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9260

lemma sg29755 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9260

lemma sg29756 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9260

lemma sg29757 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8875 sg9039

lemma sg29758 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1723 sg18249

lemma sg29759 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1835 sg17109

lemma sg29760 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2203 sg15563

lemma sg29761 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2234 sg15529

lemma sg29762 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2678 sg15016

lemma sg29763 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2868 sg14860

lemma sg29764 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4769 sg12929

lemma sg29765 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3517 sg14683

lemma sg29766 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5660 sg12603

lemma sg29767 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4769 sg12930

lemma sg29768 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2204 sg15563

lemma sg29769 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2235 sg15529

lemma sg29770 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2679 sg15016

lemma sg29771 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14860

lemma sg29772 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5250 sg12694

lemma sg29773 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5591 sg12611

lemma sg29774 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9248

lemma sg29775 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5626 sg12604

lemma sg29776 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8755 sg9480

lemma sg29777 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14515

lemma sg29778 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4572 sg13501

lemma sg29779 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6974 sg11469

lemma sg29780 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6576 sg11540

lemma sg29781 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9283

lemma sg29782 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9335

lemma sg29783 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8729 sg9546

lemma sg29784 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6975 sg11469

lemma sg29785 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6937 sg11475

lemma sg29786 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9250

lemma sg29787 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9283

lemma sg29788 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9909

lemma sg29789 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9546

lemma sg29790 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9251

lemma sg29791 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8877 sg9027

lemma sg29792 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10797

lemma sg29793 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8720 sg9606

lemma sg29794 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9943

lemma sg29795 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10157

lemma sg29796 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9943

lemma sg29797 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9283

lemma sg29798 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15529

lemma sg29799 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14515

lemma sg29800 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4573 sg13501

lemma sg29801 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6976 sg11469

lemma sg29802 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6578 sg11540

lemma sg29803 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8827 sg9219

lemma sg29804 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9335

lemma sg29805 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9546

lemma sg29806 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4574 sg13501

lemma sg29807 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6977 sg11469

lemma sg29808 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6938 sg11475

lemma sg29809 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9284

lemma sg29810 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9336

lemma sg29811 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9909

lemma sg29812 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9546

lemma sg29813 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6939 sg11475

lemma sg29814 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10353

lemma sg29815 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9284

lemma sg29816 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10798

lemma sg29817 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9606

lemma sg29818 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9251

lemma sg29819 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9944

lemma sg29820 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10711

lemma sg29821 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9944

lemma sg29822 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9284

lemma sg29823 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9284

lemma sg29824 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6978 sg11469

lemma sg29825 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6940 sg11475

lemma sg29826 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9285

lemma sg29827 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9337

lemma sg29828 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10799

lemma sg29829 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8722 sg9606

lemma sg29830 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9286

lemma sg29831 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9285

lemma sg29832 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9945

lemma sg29833 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10712

lemma sg29834 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9945

lemma sg29835 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9285

lemma sg29836 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9285

lemma sg29837 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9285

lemma sg29838 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10352

lemma sg29839 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9286

lemma sg29840 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9286

lemma sg29841 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9286

lemma sg29842 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9286

lemma sg29843 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9607

lemma sg29844 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10353

lemma sg29845 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9251

lemma sg29846 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14515

lemma sg29847 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4575 sg13501

lemma sg29848 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6979 sg11469

lemma sg29849 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6582 sg11540

lemma sg29850 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10354

lemma sg29851 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9336

lemma sg29852 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9248

lemma sg29853 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8756 sg9481

lemma sg29854 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6980 sg11469

lemma sg29855 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6941 sg11475

lemma sg29856 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10468

lemma sg29857 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9338

lemma sg29858 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10800

lemma sg29859 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10468

lemma sg29860 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10356

lemma sg29861 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9287

lemma sg29862 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9946

lemma sg29863 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10713

lemma sg29864 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9946

lemma sg29865 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9287

lemma sg29866 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9287

lemma sg29867 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9287

lemma sg29868 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10354

lemma sg29869 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6942 sg11475

lemma sg29870 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10382

lemma sg29871 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10382

lemma sg29872 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9947

lemma sg29873 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10382

lemma sg29874 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9947

lemma sg29875 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9288

lemma sg29876 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9288

lemma sg29877 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9288

lemma sg29878 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9288

lemma sg29879 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9608

lemma sg29880 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10355

lemma sg29881 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9915

lemma sg29882 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9609

lemma sg29883 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10356

lemma sg29884 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10353

lemma sg29885 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9289

lemma sg29886 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9289

lemma sg29887 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9289

lemma sg29888 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9289

lemma sg29889 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9289

lemma sg29890 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9916

lemma sg29891 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9610

lemma sg29892 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10357

lemma sg29893 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8809 sg9255

lemma sg29894 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8730 sg9551

lemma sg29895 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14516

lemma sg29896 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5565 sg12626

lemma sg29897 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5992 sg11832

lemma sg29898 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10469

lemma sg29899 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9338

lemma sg29900 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10801

lemma sg29901 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10469

lemma sg29902 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5993 sg11832

lemma sg29903 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10383

lemma sg29904 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10383

lemma sg29905 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9948

lemma sg29906 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10383

lemma sg29907 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9948

lemma sg29908 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9290

lemma sg29909 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9290

lemma sg29910 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9290

lemma sg29911 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9290

lemma sg29912 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9611

lemma sg29913 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10358

lemma sg29914 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9291

lemma sg29915 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9291

lemma sg29916 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9291

lemma sg29917 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9291

lemma sg29918 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9291

lemma sg29919 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9918

lemma sg29920 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9612

lemma sg29921 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10359

lemma sg29922 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9609

lemma sg29923 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9342

lemma sg29924 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9919

lemma sg29925 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9613

lemma sg29926 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10360

lemma sg29927 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9610

lemma sg29928 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9260

lemma sg29929 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8808 sg9260

lemma sg29930 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5582 sg12618

lemma sg29931 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6013 sg11829

lemma sg29932 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10384

lemma sg29933 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10384

lemma sg29934 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9949

lemma sg29935 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10384

lemma sg29936 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9949

lemma sg29937 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9292

lemma sg29938 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9292

lemma sg29939 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9292

lemma sg29940 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9292

lemma sg29941 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9292

lemma sg29942 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8828 sg9227

lemma sg29943 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8872 sg9076

lemma sg29944 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8829 sg9227

lemma sg29945 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8871 sg9077

lemma sg29946 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8828 sg9228

lemma sg29947 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8872 sg9077

lemma sg29948 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8829 sg9228

lemma sg29949 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9612

lemma sg29950 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9919

lemma sg29951 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9613

lemma sg29952 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,7,7,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9613

lemma sg29953 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1313 sg20975

lemma sg29954 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1714 sg18255

lemma sg29955 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1814 sg17136

lemma sg29956 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg21018

lemma sg29957 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg21032

lemma sg29958 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg21307

lemma sg29959 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg21308

lemma sg29960 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg21309

lemma sg29961 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg342 sg21310

lemma sg29962 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1314 sg20975

lemma sg29963 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1715 sg18255

lemma sg29964 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1815 sg17136

lemma sg29965 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2178 sg15583

lemma sg29966 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg21019

lemma sg29967 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2667 sg15030

lemma sg29968 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg559 sg21257

lemma sg29969 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg559 sg21258

lemma sg29970 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg559 sg21259

lemma sg29971 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg559 sg21260

lemma sg29972 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1315 sg20975

lemma sg29973 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1716 sg18255

lemma sg29974 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1816 sg17136

lemma sg29975 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2179 sg15583

lemma sg29976 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2222 sg15549

lemma sg29977 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2666 sg15033

lemma sg29978 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2665 sg15044

lemma sg29979 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg573 sg21224

lemma sg29980 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg573 sg21225

lemma sg29981 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg573 sg21226

lemma sg29982 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1461 sg20942

lemma sg29983 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2180 sg15583

lemma sg29984 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1823 sg17123

lemma sg29985 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2230 sg15532

lemma sg29986 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg21020

lemma sg29987 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg21033

lemma sg29988 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg865 sg21156

lemma sg29989 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg865 sg21157

lemma sg29990 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg865 sg21158

lemma sg29991 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg16203

lemma sg29992 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3867 sg14520

lemma sg29993 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2230 sg15533

lemma sg29994 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6928 sg11476

lemma sg29995 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5957 sg11838

lemma sg29996 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10385

lemma sg29997 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8355 sg10682

lemma sg29998 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1295 sg20997

lemma sg29999 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6929 sg11476

lemma sg30000 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5527 sg12634

lemma sg30001 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10470

lemma sg30002 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10385

lemma sg30003 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8649 sg9920

lemma sg30004 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6910 sg11480

lemma sg30005 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8836 sg9181

lemma sg30006 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9173

lemma sg30007 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8647 sg9950

lemma sg30008 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8842 sg9174

lemma sg30009 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10802

lemma sg30010 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10385

lemma sg30011 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10470

lemma sg30012 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1316 sg20975

lemma sg30013 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1717 sg18255

lemma sg30014 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1817 sg17136

lemma sg30015 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2181 sg15583

lemma sg30016 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2178 sg15584

lemma sg30017 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2676 sg15018

lemma sg30018 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2667 sg15032

lemma sg30019 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg574 sg21224

lemma sg30020 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg574 sg21225

lemma sg30021 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg574 sg21226

lemma sg30022 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1718 sg18255

lemma sg30023 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1818 sg17136

lemma sg30024 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2182 sg15583

lemma sg30025 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2223 sg15547

lemma sg30026 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2668 sg15030

lemma sg30027 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2666 sg15034

lemma sg30028 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3513 sg14691

lemma sg30029 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg866 sg21156

lemma sg30030 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg866 sg21157

lemma sg30031 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg866 sg21158

lemma sg30032 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2183 sg15583

lemma sg30033 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2180 sg15584

lemma sg30034 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3868 sg14520

lemma sg30035 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2230 sg15535

lemma sg30036 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6930 sg11476

lemma sg30037 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5958 sg11838

lemma sg30038 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10361

lemma sg30039 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8357 sg10682

lemma sg30040 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3870 sg14517

lemma sg30041 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2231 sg15533

lemma sg30042 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6931 sg11476

lemma sg30043 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5528 sg12634

lemma sg30044 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10386

lemma sg30045 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8434 sg10308

lemma sg30046 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8651 sg9920

lemma sg30047 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6932 sg11476

lemma sg30048 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6911 sg11480

lemma sg30049 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10471

lemma sg30050 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10386

lemma sg30051 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8649 sg9921

lemma sg30052 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8453 sg10264

lemma sg30053 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8837 sg9181

lemma sg30054 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9951

lemma sg30055 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9921

lemma sg30056 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10803

lemma sg30057 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10471

lemma sg30058 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9951

lemma sg30059 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1819 sg17136

lemma sg30060 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2184 sg15583

lemma sg30061 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2232 sg15531

lemma sg30062 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3869 sg14520

lemma sg30063 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2867 sg14861

lemma sg30064 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6933 sg11476

lemma sg30065 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5959 sg11838

lemma sg30066 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8437 sg10285

lemma sg30067 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8359 sg10682

lemma sg30068 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2233 sg15531

lemma sg30069 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3883 sg14509

lemma sg30070 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2223 sg15548

lemma sg30071 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6934 sg11476

lemma sg30072 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5529 sg12634

lemma sg30073 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10362

lemma sg30074 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10285

lemma sg30075 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8652 sg9920

lemma sg30076 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3870 sg14518

lemma sg30077 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6935 sg11476

lemma sg30078 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6912 sg11480

lemma sg30079 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10387

lemma sg30080 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9293

lemma sg30081 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8726 sg9557

lemma sg30082 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6569 sg11542

lemma sg30083 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10472

lemma sg30084 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10387

lemma sg30085 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9922

lemma sg30086 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8727 sg9557

lemma sg30087 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9240

lemma sg30088 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10804

lemma sg30089 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10472

lemma sg30090 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10387

lemma sg30091 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9952

lemma sg30092 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3164 sg14803

lemma sg30093 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3770 sg14539

lemma sg30094 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6936 sg11476

lemma sg30095 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6913 sg11480

lemma sg30096 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10363

lemma sg30097 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9261

lemma sg30098 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8657 sg9780

lemma sg30099 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6995 sg11467

lemma sg30100 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5960 sg11838

lemma sg30101 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10388

lemma sg30102 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9294

lemma sg30103 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9261

lemma sg30104 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8736 sg9541

lemma sg30105 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10473

lemma sg30106 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10388

lemma sg30107 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10805

lemma sg30108 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10473

lemma sg30109 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9953

lemma sg30110 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10388

lemma sg30111 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9953

lemma sg30112 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10363

lemma sg30113 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6014 sg11827

lemma sg30114 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10474

lemma sg30115 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9295

lemma sg30116 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10806

lemma sg30117 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10474

lemma sg30118 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10389

lemma sg30119 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9954

lemma sg30120 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10389

lemma sg30121 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9954

lemma sg30122 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9924

lemma sg30123 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10364

lemma sg30124 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9925

lemma sg30125 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9925

lemma sg30126 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10365

lemma sg30127 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,4,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9263

lemma sg30128 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1319 sg20973

lemma sg30129 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1722 sg18251

lemma sg30130 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1825 sg17122

lemma sg30131 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2191 sg15571

lemma sg30132 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15547

lemma sg30133 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2677 sg15018

lemma sg30134 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2676 sg15020

lemma sg30135 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14690

lemma sg30136 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg867 sg21156

lemma sg30137 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg867 sg21157

lemma sg30138 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg867 sg21158

lemma sg30139 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1826 sg17122

end UniversalTensorSquare
end
end

end OAI
