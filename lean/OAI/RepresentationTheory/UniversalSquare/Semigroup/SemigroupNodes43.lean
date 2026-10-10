import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37

namespace OAI

/-! Semigroup Nodes 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg17740 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13932

lemma sg17741 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13933

lemma sg17742 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13934

lemma sg17743 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13935

lemma sg17744 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14956

lemma sg17745 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14957

lemma sg17746 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg14958

lemma sg17747 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13936

lemma sg17748 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13937

lemma sg17749 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13938

lemma sg17750 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13939

lemma sg17751 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13940

lemma sg17752 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13941

lemma sg17753 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg13 sg13942

lemma sg17754 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg1 sg14959

lemma sg17755 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14960

lemma sg17756 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13943

lemma sg17757 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14961

lemma sg17758 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14962

lemma sg17759 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg14963

lemma sg17760 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13944

lemma sg17761 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12469

lemma sg17762 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13945

lemma sg17763 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13946

lemma sg17764 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14964

lemma sg17765 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg83 sg12355

lemma sg17766 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13947

lemma sg17767 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg56 sg12470

lemma sg17768 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12471

lemma sg17769 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13948

lemma sg17770 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg84 sg12341

lemma sg17771 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,5] := by
  exact rowSquare_join (by decide) sg1 sg14965

lemma sg17772 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13949

lemma sg17773 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12472

lemma sg17774 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg84 sg12342

lemma sg17775 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,4] := by
  exact rowSquare_join (by decide) sg84 sg12343

lemma sg17776 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14966

lemma sg17777 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13777

lemma sg17778 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14967

lemma sg17779 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13780

lemma sg17780 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13950

lemma sg17781 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13783

lemma sg17782 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13786

lemma sg17783 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13951

lemma sg17784 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13952

lemma sg17785 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13953

lemma sg17786 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13954

lemma sg17787 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg13795

lemma sg17788 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13796

lemma sg17789 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13955

lemma sg17790 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13800

lemma sg17791 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13956

lemma sg17792 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13957

lemma sg17793 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13810

lemma sg17794 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg14 sg13811

lemma sg17795 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13958

lemma sg17796 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12480

lemma sg17797 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13959

lemma sg17798 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg84 sg12344

lemma sg17799 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,5] := by
  exact rowSquare_join (by decide) sg14 sg13818

lemma sg17800 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14968

lemma sg17801 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13960

lemma sg17802 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg14969

lemma sg17803 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13961

lemma sg17804 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12483

lemma sg17805 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg83 sg12356

lemma sg17806 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg83 sg12357

lemma sg17807 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13962

lemma sg17808 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12484

lemma sg17809 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,3,1] := by
  exact rowSquare_join (by decide) sg84 sg12345

lemma sg17810 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,4] := by
  exact rowSquare_join (by decide) sg84 sg12346

lemma sg17811 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13963

lemma sg17812 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12347

lemma sg17813 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,3] := by
  exact rowSquare_join (by decide) sg84 sg12348

lemma sg17814 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13829

lemma sg17815 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13964

lemma sg17816 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13965

lemma sg17817 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13839

lemma sg17818 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg14 sg13840

lemma sg17819 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13848

lemma sg17820 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg57 sg12480

lemma sg17821 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13966

lemma sg17822 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,4,1] := by
  exact rowSquare_join (by decide) sg14 sg13854

lemma sg17823 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13967

lemma sg17824 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13968

lemma sg17825 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13969

lemma sg17826 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,5,5,4] := by
  exact rowSquare_join (by decide) sg13 sg13970

lemma sg17827 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12366

lemma sg17828 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,3,3,2] := by
  exact rowSquare_join (by decide) sg83 sg12367

lemma sg17829 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12492

lemma sg17830 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,2] := by
  exact rowSquare_join (by decide) sg83 sg12368

lemma sg17831 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,3,1] := by
  exact rowSquare_join (by decide) sg83 sg12369

lemma sg17832 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,4,4] := by
  exact rowSquare_join (by decide) sg83 sg12370

lemma sg17833 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13971

lemma sg17834 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,5,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13972

lemma sg17835 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,5,3] := by
  exact rowSquare_join (by decide) sg13 sg13973

lemma sg17836 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,6,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13974

lemma sg17837 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,8,6,6,2] := by
  exact rowSquare_join (by decide) sg13 sg13975

lemma sg17838 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3676 sg4117

lemma sg17839 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13867

lemma sg17840 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13976

lemma sg17841 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3676 sg4118

lemma sg17842 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13870

lemma sg17843 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13871

lemma sg17844 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13872

lemma sg17845 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4484

lemma sg17846 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13977

lemma sg17847 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13978

lemma sg17848 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13877

lemma sg17849 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13878

lemma sg17850 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13979

lemma sg17851 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13980

lemma sg17852 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13981

lemma sg17853 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13982

lemma sg17854 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,9,4,4,4,1] := by
  exact rowSquare_join (by decide) sg14 sg13883

lemma sg17855 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14970

lemma sg17856 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14971

lemma sg17857 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8 sg14125

lemma sg17858 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13983

lemma sg17859 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14972

lemma sg17860 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg15 sg13679

lemma sg17861 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8 sg14126

lemma sg17862 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8 sg14127

lemma sg17863 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14973

lemma sg17864 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13985

lemma sg17865 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14974

lemma sg17866 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg15 sg13689

lemma sg17867 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14975

lemma sg17868 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13987

lemma sg17869 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13988

lemma sg17870 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg15 sg13700

lemma sg17871 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13991

lemma sg17872 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13992

lemma sg17873 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13993

lemma sg17874 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg84 sg12355

lemma sg17875 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg15 sg13708

lemma sg17876 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg13921

lemma sg17877 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13997

lemma sg17878 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg15 sg13732

lemma sg17879 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,4,4,2] := by
  exact rowSquare_join (by decide) sg15 sg13733

lemma sg17880 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12490

lemma sg17881 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg84 sg12356

lemma sg17882 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg84 sg12357

lemma sg17883 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,5,5,5] := by
  exact rowSquare_join (by decide) sg15 sg13739

lemma sg17884 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg83 sg12394

lemma sg17885 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12358

lemma sg17886 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,4,3,2] := by
  exact rowSquare_join (by decide) sg84 sg12359

lemma sg17887 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,4,4,1] := by
  exact rowSquare_join (by decide) sg83 sg12396

lemma sg17888 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12360

lemma sg17889 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12361

lemma sg17890 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg84 sg12362

lemma sg17891 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,5,4] := by
  exact rowSquare_join (by decide) sg84 sg12363

lemma sg17892 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12491

lemma sg17893 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,6,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12364

lemma sg17894 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,6,6,6,3] := by
  exact rowSquare_join (by decide) sg84 sg12365

lemma sg17895 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,4,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13999

lemma sg17896 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13941

lemma sg17897 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,4,4,4,2] := by
  exact rowSquare_join (by decide) sg14 sg13942

lemma sg17898 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,5,3,3,3] := by
  exact rowSquare_join (by decide) sg83 sg12397

lemma sg17899 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12366

lemma sg17900 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,5,4,3,2] := by
  exact rowSquare_join (by decide) sg84 sg12367

lemma sg17901 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,5,4,4,1] := by
  exact rowSquare_join (by decide) sg85 sg12341

lemma sg17902 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12492

lemma sg17903 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,5,5,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12368

lemma sg17904 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,5,5,3,1] := by
  exact rowSquare_join (by decide) sg84 sg12369

lemma sg17905 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,5,5,4] := by
  exact rowSquare_join (by decide) sg84 sg12370

lemma sg17906 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12399

lemma sg17907 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,3,3,2] := by
  exact rowSquare_join (by decide) sg295 sg11062

lemma sg17908 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12371

lemma sg17909 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,4,2,2] := by
  exact rowSquare_join (by decide) sg295 sg11063

lemma sg17910 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,4,3,1] := by
  exact rowSquare_join (by decide) sg295 sg11064

lemma sg17911 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,4,4] := by
  exact rowSquare_join (by decide) sg83 sg12404

lemma sg17912 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12374

lemma sg17913 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,5,2,1] := by
  exact rowSquare_join (by decide) sg295 sg11065

lemma sg17914 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,5,3] := by
  exact rowSquare_join (by decide) sg84 sg12376

lemma sg17915 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,6,1,1] := by
  exact rowSquare_join (by decide) sg295 sg11066

lemma sg17916 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,7,6,6,2] := by
  exact rowSquare_join (by decide) sg84 sg12378

lemma sg17917 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,4,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13957

lemma sg17918 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12495

lemma sg17919 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,4,4,3,2] := by
  exact rowSquare_join (by decide) sg84 sg12379

lemma sg17920 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,4,4,4,1] := by
  exact rowSquare_join (by decide) sg85 sg12344

lemma sg17921 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12409

lemma sg17922 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,5,3,3,2] := by
  exact rowSquare_join (by decide) sg295 sg11067

lemma sg17923 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12380

lemma sg17924 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,5,4,2,2] := by
  exact rowSquare_join (by decide) sg295 sg11068

lemma sg17925 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,5,4,3,1] := by
  exact rowSquare_join (by decide) sg295 sg11069

lemma sg17926 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,5,4,4] := by
  exact rowSquare_join (by decide) sg57 sg12493

lemma sg17927 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12496

lemma sg17928 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,5,5,2,1] := by
  exact rowSquare_join (by decide) sg295 sg11070

lemma sg17929 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,5,5,3] := by
  exact rowSquare_join (by decide) sg84 sg12384

lemma sg17930 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12385

lemma sg17931 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,6,3,2,2] := by
  exact rowSquare_join (by decide) sg295 sg11071

lemma sg17932 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,6,3,3,1] := by
  exact rowSquare_join (by decide) sg295 sg11072

lemma sg17933 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12387

lemma sg17934 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,6,4,2,1] := by
  exact rowSquare_join (by decide) sg295 sg11073

lemma sg17935 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,6,4,3] := by
  exact rowSquare_join (by decide) sg296 sg11069

lemma sg17936 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,6,5,1,1] := by
  exact rowSquare_join (by decide) sg295 sg11074

lemma sg17937 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,6,5,2] := by
  exact rowSquare_join (by decide) sg296 sg11070

lemma sg17938 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,8,6,6,1] := by
  exact rowSquare_join (by decide) sg297 sg11070

lemma sg17939 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,9,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13965

lemma sg17940 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,9,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg57 sg12495

lemma sg17941 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,9,4,3,3,2] := by
  exact rowSquare_join (by decide) sg295 sg11076

lemma sg17942 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,9,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14000

lemma sg17943 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,9,4,4,2,2] := by
  exact rowSquare_join (by decide) sg295 sg11077

lemma sg17944 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,9,4,4,3,1] := by
  exact rowSquare_join (by decide) sg295 sg11078

lemma sg17945 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,9,4,4,4] := by
  exact rowSquare_join (by decide) sg14 sg13970

lemma sg17946 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13978

lemma sg17947 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14001

lemma sg17948 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13981

lemma sg17949 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,3,3,3,2] := by
  exact rowSquare_join (by decide) sg295 sg11080

lemma sg17950 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg55 sg12505

lemma sg17951 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14002

lemma sg17952 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,4,3,2,2] := by
  exact rowSquare_join (by decide) sg295 sg11081

lemma sg17953 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,4,3,3,1] := by
  exact rowSquare_join (by decide) sg295 sg11082

lemma sg17954 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14003

lemma sg17955 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,4,4,2,1] := by
  exact rowSquare_join (by decide) sg295 sg11083

lemma sg17956 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [10,10,4,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14004

lemma sg17957 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg15 sg13765

lemma sg17958 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14005

lemma sg17959 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg15 sg13774

lemma sg17960 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg15 sg13775

lemma sg17961 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg15 sg13776

lemma sg17962 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13984

lemma sg17963 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg15 sg13786

lemma sg17964 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14006

lemma sg17965 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14007

lemma sg17966 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg15 sg13794

lemma sg17967 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg15 sg13795

lemma sg17968 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg15 sg13802

lemma sg17969 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg15 sg13803

lemma sg17970 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12497

lemma sg17971 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12393

lemma sg17972 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg84 sg12394

lemma sg17973 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg15 sg13810

lemma sg17974 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg15 sg13811

lemma sg17975 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg56 sg12498

lemma sg17976 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg56 sg12499

lemma sg17977 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg84 sg12395

lemma sg17978 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg84 sg12396

lemma sg17979 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,5,5,5,5] := by
  exact rowSquare_join (by decide) sg15 sg13818

lemma sg17980 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13986

lemma sg17981 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13989

lemma sg17982 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13990

lemma sg17983 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12500

lemma sg17984 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14008

lemma sg17985 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg84 sg12397

lemma sg17986 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13993

lemma sg17987 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg85 sg12355

lemma sg17988 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12501

lemma sg17989 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12428

lemma sg17990 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,3,3,3] := by
  exact rowSquare_join (by decide) sg295 sg11085

lemma sg17991 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12398

lemma sg17992 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12399

lemma sg17993 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg295 sg11086

lemma sg17994 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg295 sg11087

lemma sg17995 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12401

lemma sg17996 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg295 sg11088

lemma sg17997 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg295 sg11089

lemma sg17998 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,5,5,4] := by
  exact rowSquare_join (by decide) sg84 sg12404

lemma sg17999 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg239 sg11140

lemma sg18000 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg239 sg11141

lemma sg18001 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11142

lemma sg18002 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,3,3,2] := by
  exact rowSquare_join (by decide) sg298 sg11062

lemma sg18003 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12406

lemma sg18004 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,4,2,2] := by
  exact rowSquare_join (by decide) sg298 sg11063

lemma sg18005 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,4,3,1] := by
  exact rowSquare_join (by decide) sg298 sg11064

lemma sg18006 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,4,4] := by
  exact rowSquare_join (by decide) sg762 sg8020

lemma sg18007 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12408

lemma sg18008 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,5,2,1] := by
  exact rowSquare_join (by decide) sg298 sg11065

lemma sg18009 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,5,3] := by
  exact rowSquare_join (by decide) sg762 sg8021

lemma sg18010 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,6,1,1] := by
  exact rowSquare_join (by decide) sg298 sg11066

lemma sg18011 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,6,6,6,2] := by
  exact rowSquare_join (by decide) sg762 sg8022

lemma sg18012 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13994

lemma sg18013 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13995

lemma sg18014 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12502

lemma sg18015 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,7,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13996

lemma sg18016 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg295 sg11090

lemma sg18017 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg56 sg12503

lemma sg18018 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,7,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12409

lemma sg18019 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,7,4,4,3,2] := by
  exact rowSquare_join (by decide) sg295 sg11091

lemma sg18020 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,7,4,4,4,1] := by
  exact rowSquare_join (by decide) sg295 sg11092

lemma sg18021 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,8,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg56 sg12504

lemma sg18022 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,8,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13998

lemma sg18023 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,8,3,3,3,3] := by
  exact rowSquare_join (by decide) sg295 sg11093

lemma sg18024 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,8,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg239 sg11146

lemma sg18025 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,8,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg240 sg11144

lemma sg18026 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [11,8,4,4,4] := by
  exact rowSquare_join (by decide) sg762 sg8023

lemma sg18027 : RowSquare [6,6,3,3,2,2,2,2,2,2,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg8780

lemma sg18028 : RowSquare [6,6,3,3,2,2,2,2,2,2,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg8781

lemma sg18029 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14013

lemma sg18030 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg2624 sg4949

lemma sg18031 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3318 sg4438

lemma sg18032 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg3554 sg4186

lemma sg18033 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,2] := by
  exact rowSquare_join (by decide) sg3675 sg4034

lemma sg18034 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12822

lemma sg18035 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg13 sg14016

lemma sg18036 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg13 sg14017

lemma sg18037 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3556 sg4186

lemma sg18038 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14013

lemma sg18039 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg3679 sg4034

lemma sg18040 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg13 sg14019

lemma sg18041 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg3556 sg4187

lemma sg18042 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14020

lemma sg18043 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,4,1] := by
  exact rowSquare_join (by decide) sg13 sg14021

lemma sg18044 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg14022

lemma sg18045 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg55 sg12509

lemma sg18046 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg3319 sg4438

lemma sg18047 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg55 sg12514

lemma sg18048 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1757 sg6491

lemma sg18049 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg1675 sg6507

lemma sg18050 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg15 sg14010

lemma sg18051 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg14986

lemma sg18052 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1 sg14987

lemma sg18053 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg26 sg12823

lemma sg18054 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1 sg14988

lemma sg18055 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg13 sg14023

lemma sg18056 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg1 sg14989

lemma sg18057 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1 sg14990

lemma sg18058 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14024

lemma sg18059 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg14 sg14014

lemma sg18060 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg27 sg12823

lemma sg18061 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg14991

lemma sg18062 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg26 sg12824

lemma sg18063 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14992

lemma sg18064 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1 sg14993

lemma sg18065 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg14994

lemma sg18066 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg26 sg12825

lemma sg18067 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg165 sg11584

lemma sg18068 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,5] := by
  exact rowSquare_join (by decide) sg56 sg12514

lemma sg18069 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg14015

lemma sg18070 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg26 sg12826

lemma sg18071 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2640 sg4934

lemma sg18072 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg27 sg12824

lemma sg18073 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg26 sg12827

lemma sg18074 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg26 sg12828

lemma sg18075 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,5,1] := by
  exact rowSquare_join (by decide) sg165 sg11585

lemma sg18076 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg55 sg12521

lemma sg18077 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,5] := by
  exact rowSquare_join (by decide) sg166 sg11584

lemma sg18078 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg14018

lemma sg18079 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg27 sg12826

lemma sg18080 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14025

lemma sg18081 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14026

lemma sg18082 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3679 sg4035

lemma sg18083 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg15 sg14011

lemma sg18084 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg15 sg14012

lemma sg18085 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg26 sg12829

lemma sg18086 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1 sg14995

lemma sg18087 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg28 sg12823

lemma sg18088 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg14996

lemma sg18089 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg26 sg12830

lemma sg18090 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg15 sg14013

lemma sg18091 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg165 sg11586

lemma sg18092 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg27 sg12829

lemma sg18093 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg14 sg14023

lemma sg18094 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg27 sg12830

lemma sg18095 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg56 sg12521

lemma sg18096 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg165 sg11587

lemma sg18097 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg55 sg12535

lemma sg18098 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,5] := by
  exact rowSquare_join (by decide) sg168 sg11584

lemma sg18099 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg14024

lemma sg18100 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg29 sg12824

lemma sg18101 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,5] := by
  exact rowSquare_join (by decide) sg166 sg11587

lemma sg18102 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,4,1] := by
  exact rowSquare_join (by decide) sg295 sg11097

lemma sg18103 : RowSquare [6,6,4,3,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg26 sg12831

lemma sg18104 : RowSquare [6,6,4,3,3,2,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3556 sg3992

lemma sg18105 : RowSquare [6,6,4,3,3,2,1,1,1,1,1,1,1] [7,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg165 sg11588

lemma sg18106 : RowSquare [6,6,4,3,3,2,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3556 sg3993

lemma sg18107 : RowSquare [6,6,4,3,3,2,1,1,1,1,1,1,1] [8,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg14699

lemma sg18108 : RowSquare [6,6,4,3,3,2,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1 sg15003

lemma sg18109 : RowSquare [6,6,4,3,3,2,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg165 sg11590

lemma sg18110 : RowSquare [6,6,4,3,3,2,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg165 sg11592

lemma sg18111 : RowSquare [6,6,4,3,3,2,1,1,1,1,1,1,1] [8,8,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg14030

lemma sg18112 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4918

lemma sg18113 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2704 sg4918

lemma sg18114 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4924

lemma sg18115 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg5755

lemma sg18116 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2252 sg5755

lemma sg18117 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3622 sg4164

lemma sg18118 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg3623 sg4167

lemma sg18119 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg3615 sg4168

lemma sg18120 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3626 sg4166

lemma sg18121 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3630 sg4162

lemma sg18122 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg3620 sg4173

lemma sg18123 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14647

lemma sg18124 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14648

lemma sg18125 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,3] := by
  exact rowSquare_join (by decide) sg3620 sg4174

lemma sg18126 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14031

lemma sg18127 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14032

lemma sg18128 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3622 sg4171

lemma sg18129 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,2,1] := by
  exact rowSquare_join (by decide) sg3621 sg4172

lemma sg18130 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14033

lemma sg18131 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg3622 sg4172

lemma sg18132 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg13 sg14034

lemma sg18133 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3622 sg4174

lemma sg18134 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,4] := by
  exact rowSquare_join (by decide) sg0 sg15551

lemma sg18135 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15552

lemma sg18136 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg0 sg15553

lemma sg18137 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14651

lemma sg18138 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg39 sg12766

lemma sg18139 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14036

end UniversalTensorSquare
end
end

end OAI
