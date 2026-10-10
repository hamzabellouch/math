import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes14
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes7

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7734 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3813

lemma sg7735 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg3814

lemma sg7736 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg5405

lemma sg7737 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg610 sg1328

lemma sg7738 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5406

lemma sg7739 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5407

lemma sg7740 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg3803

lemma sg7741 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg4655

lemma sg7742 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5408

lemma sg7743 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3815

lemma sg7744 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4665

lemma sg7745 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3816

lemma sg7746 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg3817

lemma sg7747 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4666

lemma sg7748 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3818

lemma sg7749 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,4,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4667

lemma sg7750 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg3819

lemma sg7751 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg3820

lemma sg7752 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5409

lemma sg7753 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5410

lemma sg7754 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3821

lemma sg7755 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg3805

lemma sg7756 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg3806

lemma sg7757 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3822

lemma sg7758 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg3807

lemma sg7759 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg3823

lemma sg7760 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4668

lemma sg7761 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg3824

lemma sg7762 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg3825

lemma sg7763 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4669

lemma sg7764 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,5,5,2] := by
  exact rowSquare_join (by decide) sg13 sg3826

lemma sg7765 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5411

lemma sg7766 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4670

lemma sg7767 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3827

lemma sg7768 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5412

lemma sg7769 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg3809

lemma sg7770 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg3828

lemma sg7771 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,3,3] := by
  exact rowSquare_join (by decide) sg13 sg3829

lemma sg7772 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg3811

lemma sg7773 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,4,2] := by
  exact rowSquare_join (by decide) sg13 sg3830

lemma sg7774 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,6,5,1] := by
  exact rowSquare_join (by decide) sg13 sg3831

lemma sg7775 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,7,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6286

lemma sg7776 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,7,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4671

lemma sg7777 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,7,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6287

lemma sg7778 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,7,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4672

lemma sg7779 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg312 sg1754

lemma sg7780 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg1754

lemma sg7781 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1327

lemma sg7782 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg889

lemma sg7783 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg314 sg1754

lemma sg7784 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg536 sg1327

lemma sg7785 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg890

lemma sg7786 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1754

lemma sg7787 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg537 sg1327

lemma sg7788 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg891

lemma sg7789 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg892

lemma sg7790 : RowSquare [6,5,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg316 sg1754

lemma sg7791 : RowSquare [6,5,2,1,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg319 sg1754

lemma sg7792 : RowSquare [6,5,2,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg541 sg1327

lemma sg7793 : RowSquare [6,5,2,1,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg543 sg1327

lemma sg7794 : RowSquare [6,5,2,1,1,1,1,1,1,1] [4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1757

lemma sg7795 : RowSquare [6,5,2,1,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg808

lemma sg7796 : RowSquare [6,5,2,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg809

lemma sg7797 : RowSquare [6,5,2,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg321 sg1754

lemma sg7798 : RowSquare [6,5,2,1,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg1754

lemma sg7799 : RowSquare [6,5,2,1,1,1,1,1,1,1] [7,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg328 sg1754

lemma sg7800 : RowSquare [6,5,2,1,1,1,1,1,1,1] [7,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg329 sg1754

lemma sg7801 : RowSquare [6,5,2,2,2,2,1] [5,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5681

lemma sg7802 : RowSquare [6,5,2,2,2,2,1] [5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5682

lemma sg7803 : RowSquare [6,5,2,2,2,2,1] [5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5683

lemma sg7804 : RowSquare [6,5,2,2,2,2,1] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5684

lemma sg7805 : RowSquare [6,6,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg518 sg1327

lemma sg7806 : RowSquare [6,6,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg889 sg889

lemma sg7807 : RowSquare [6,6,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg892 sg892

lemma sg7808 : RowSquare [6,6,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg521 sg1327

lemma sg7809 : RowSquare [6,6,1,1,1,1,1,1,1,1] [5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg895 sg892

lemma sg7810 : RowSquare [6,6,1,1,1,1,1,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg13 sg3875

lemma sg7811 : RowSquare [6,6,2,1,1,1,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg13 sg3916

lemma sg7813 : RowSquare [6,6,2,2,2,2] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg788 sg789

lemma sg7814 : RowSquare [6,6,2,2,2,2] [2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg787 sg789

lemma sg7815 : RowSquare [6,6,2,2,2,2] [2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg785 sg789

lemma sg7816 : RowSquare [6,6,2,2,2,2] [2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg780 sg789

lemma sg7817 : RowSquare [6,6,2,2,2,2] [2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg780 sg788

lemma sg7818 : RowSquare [6,6,2,2,2,2] [2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg780 sg787

lemma sg7819 : RowSquare [6,6,2,2,2,2] [2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg780 sg785

lemma sg7820 : RowSquare [6,6,2,2,2,2] [2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg780 sg782

lemma sg7821 : RowSquare [6,6,2,2,2,2] [2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg780 sg780

lemma sg7822 : RowSquare [6,6,2,2,2,2] [3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg786 sg789

lemma sg7823 : RowSquare [6,6,2,2,2,2] [3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg784 sg789

lemma sg7824 : RowSquare [6,6,2,2,2,2] [3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg779 sg788

lemma sg7825 : RowSquare [6,6,2,2,2,2] [3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg779 sg787

lemma sg7826 : RowSquare [6,6,2,2,2,2] [3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg779 sg785

lemma sg7827 : RowSquare [6,6,2,2,2,2] [3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg779 sg782

lemma sg7828 : RowSquare [6,6,2,2,2,2] [3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg779 sg780

lemma sg7829 : RowSquare [6,6,2,2,2,2] [3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg781 sg789

lemma sg7830 : RowSquare [6,6,2,2,2,2] [3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg778 sg789

lemma sg7831 : RowSquare [6,6,2,2,2,2] [3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg775 sg788

lemma sg7832 : RowSquare [6,6,2,2,2,2] [3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg775 sg787

lemma sg7833 : RowSquare [6,6,2,2,2,2] [3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg775 sg785

lemma sg7834 : RowSquare [6,6,2,2,2,2] [3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg775 sg782

lemma sg7835 : RowSquare [6,6,2,2,2,2] [3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg775 sg780

lemma sg7836 : RowSquare [6,6,2,2,2,2] [3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg773 sg787

lemma sg7837 : RowSquare [6,6,2,2,2,2] [3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg773 sg781

lemma sg7838 : RowSquare [6,6,2,2,2,2] [3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg773 sg778

lemma sg7839 : RowSquare [6,6,2,2,2,2] [3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg773 sg775

lemma sg7840 : RowSquare [6,6,2,2,2,2] [3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg773 sg773

lemma sg7841 : RowSquare [6,6,2,2,2,2] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg783 sg789

lemma sg7842 : RowSquare [6,6,2,2,2,2] [4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg774 sg788

lemma sg7843 : RowSquare [6,6,2,2,2,2] [4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg774 sg787

lemma sg7844 : RowSquare [6,6,2,2,2,2] [4,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg774 sg785

lemma sg7845 : RowSquare [6,6,2,2,2,2] [4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg774 sg782

lemma sg7846 : RowSquare [6,6,2,2,2,2] [4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg774 sg780

lemma sg7847 : RowSquare [6,6,2,2,2,2] [4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg777 sg789

lemma sg7848 : RowSquare [6,6,2,2,2,2] [4,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg772 sg787

lemma sg7849 : RowSquare [6,6,2,2,2,2] [4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg772 sg785

lemma sg7850 : RowSquare [6,6,2,2,2,2] [4,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg772 sg782

lemma sg7851 : RowSquare [6,6,2,2,2,2] [4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg772 sg780

lemma sg7852 : RowSquare [6,6,2,2,2,2] [4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg768 sg778

lemma sg7853 : RowSquare [6,6,2,2,2,2] [5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg771 sg789

lemma sg7854 : RowSquare [6,6,2,2,2,2] [5,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg771 sg787

lemma sg7855 : RowSquare [6,6,2,2,2,2] [5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg771 sg785

lemma sg7856 : RowSquare [6,6,2,2,2,2] [5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg771 sg782

lemma sg7857 : RowSquare [6,6,2,2,2,2] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg771 sg780

lemma sg7858 : RowSquare [6,6,2,2,2,2] [5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg766 sg784

lemma sg7859 : RowSquare [7,5,2,1,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg51 sg2702

lemma sg7860 : RowSquare [7,5,2,1,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg53 sg2702

lemma sg7861 : RowSquare [7,5,2,2,2,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg3959

lemma sg7862 : RowSquare [7,5,2,2,2,1,1] [5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg537 sg1146

lemma sg7863 : RowSquare [7,5,2,2,2,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg270 sg1636

lemma sg7864 : RowSquare [7,5,2,2,2,1,1] [5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg537 sg1147

lemma sg7865 : RowSquare [7,5,2,2,2,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5607

lemma sg7866 : RowSquare [7,5,2,2,2,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4797

lemma sg7867 : RowSquare [7,5,2,2,2,1,1] [6,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4801

lemma sg7868 : RowSquare [7,5,2,2,2,1,1] [6,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3960

lemma sg7869 : RowSquare [7,5,2,2,2,1,1] [6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5608

lemma sg7870 : RowSquare [7,5,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5609

lemma sg7871 : RowSquare [7,5,2,2,2,1,1] [6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5610

lemma sg7872 : RowSquare [7,5,2,2,2,1,1] [6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg5611

lemma sg7873 : RowSquare [7,5,2,2,2,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4798

lemma sg7874 : RowSquare [7,5,2,2,2,1,1] [6,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg3937

lemma sg7875 : RowSquare [7,5,2,2,2,1,1] [6,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6453

lemma sg7876 : RowSquare [7,5,2,2,2,1,1] [6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6454

lemma sg7877 : RowSquare [7,5,2,2,2,1,1] [6,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6455

lemma sg7878 : RowSquare [7,5,2,2,2,1,1] [6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6456

lemma sg7879 : RowSquare [7,5,2,2,2,1,1] [6,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg3938

lemma sg7880 : RowSquare [7,5,2,2,2,1,1] [6,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg3200

lemma sg7881 : RowSquare [7,5,2,2,2,1,1] [6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4802

lemma sg7882 : RowSquare [7,5,2,2,2,1,1] [6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg534 sg1149

lemma sg7883 : RowSquare [7,5,2,2,2,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4803

lemma sg7884 : RowSquare [7,5,2,2,2,1,1] [6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg3201

lemma sg7885 : RowSquare [7,5,2,2,2,1,1] [6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg534 sg1150

lemma sg7886 : RowSquare [7,5,2,2,2,1,1] [6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg272 sg1633

lemma sg7887 : RowSquare [7,5,2,2,2,1,1] [6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg538 sg1146

lemma sg7888 : RowSquare [7,5,2,2,2,1,1] [6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg272 sg1634

lemma sg7889 : RowSquare [7,5,2,2,2,1,1] [6,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg3937

lemma sg7890 : RowSquare [7,5,2,2,2,1,1] [6,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg3939

lemma sg7891 : RowSquare [7,5,2,2,2,1,1] [6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg3202

lemma sg7892 : RowSquare [7,5,2,2,2,1,1] [6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4799

lemma sg7893 : RowSquare [7,5,2,2,2,1,1] [6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg534 sg1151

lemma sg7894 : RowSquare [7,5,2,2,2,1,1] [6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg4800

lemma sg7895 : RowSquare [7,5,2,2,2,1,1] [6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg3200

lemma sg7896 : RowSquare [7,5,2,2,2,1,1] [6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg3203

lemma sg7897 : RowSquare [7,5,2,2,2,1,1] [6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg735

lemma sg7898 : RowSquare [7,5,2,2,2,1,1] [6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg535 sg1149

lemma sg7899 : RowSquare [7,5,2,2,2,1,1] [6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg736

lemma sg7900 : RowSquare [7,5,2,2,2,1,1] [6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1150

lemma sg7901 : RowSquare [7,5,2,2,2,1,1] [6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg491 sg1186

lemma sg7902 : RowSquare [7,5,2,2,2,1,1] [6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg539 sg1146

lemma sg7903 : RowSquare [7,5,2,2,2,1,1] [6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg114 sg2121

lemma sg7904 : RowSquare [7,5,2,2,2,1,1] [6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg534 sg1154

lemma sg7905 : RowSquare [7,5,2,2,2,1,1] [6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg839 sg735

lemma sg7906 : RowSquare [7,5,2,2,2,1,1] [6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg536 sg1149

lemma sg7907 : RowSquare [7,5,2,2,2,1,1] [6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg839 sg736

lemma sg7908 : RowSquare [7,5,2,2,2,1,1] [6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg840 sg735

lemma sg7909 : RowSquare [7,5,2,2,2,1,1] [6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg840 sg736

lemma sg7910 : RowSquare [7,5,2,2,2,1,1] [6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg3939

lemma sg7911 : RowSquare [7,5,2,2,2,1,1] [6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg3202

lemma sg7912 : RowSquare [7,5,2,2,2,1,1] [6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3961

lemma sg7913 : RowSquare [7,5,2,2,2,1,1] [6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg737

lemma sg7914 : RowSquare [7,5,2,2,2,1,1] [6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg535 sg1151

lemma sg7915 : RowSquare [7,5,2,2,2,1,1] [6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg114 sg2122

lemma sg7916 : RowSquare [7,5,2,2,2,1,1] [6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg738

lemma sg7917 : RowSquare [7,5,2,2,2,1,1] [6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg839 sg737

lemma sg7918 : RowSquare [7,5,2,2,2,1,1] [6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg536 sg1151

lemma sg7919 : RowSquare [7,5,2,2,2,1,1] [6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1153

lemma sg7920 : RowSquare [7,5,2,2,2,1,1] [6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg840 sg737

lemma sg7921 : RowSquare [7,5,2,2,2,1,1] [6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg739

lemma sg7922 : RowSquare [7,5,2,2,2,1,1] [6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg839 sg738

lemma sg7923 : RowSquare [7,5,2,2,2,1,1] [6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg839 sg739

lemma sg7924 : RowSquare [7,5,2,2,2,1,1] [6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg3940

lemma sg7925 : RowSquare [7,5,2,2,2,1,1] [6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg115 sg2122

lemma sg7926 : RowSquare [7,5,2,2,2,1,1] [6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg740

lemma sg7927 : RowSquare [7,5,2,2,2,1,1] [6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1155

lemma sg7928 : RowSquare [7,5,2,2,2,1,1] [6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg3941

lemma sg7929 : RowSquare [7,5,2,2,2,1,1] [6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg741

lemma sg7930 : RowSquare [7,5,2,2,2,1,1] [6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg839 sg740

lemma sg7931 : RowSquare [7,5,2,2,2,1,1] [6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg839 sg741

lemma sg7932 : RowSquare [7,5,2,2,2,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4797

lemma sg7933 : RowSquare [7,5,2,2,2,1,1] [7,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4801

lemma sg7934 : RowSquare [7,5,2,2,2,1,1] [7,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg3942

lemma sg7935 : RowSquare [7,5,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3962

lemma sg7936 : RowSquare [7,5,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5612

lemma sg7937 : RowSquare [7,5,2,2,2,1,1] [7,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5613

lemma sg7938 : RowSquare [7,5,2,2,2,1,1] [7,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg5614

lemma sg7939 : RowSquare [7,5,2,2,2,1,1] [7,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg3942

lemma sg7940 : RowSquare [7,5,2,2,2,1,1] [7,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg3943

lemma sg7941 : RowSquare [7,5,2,2,2,1,1] [7,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg3204

lemma sg7942 : RowSquare [7,5,2,2,2,1,1] [7,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4802

lemma sg7943 : RowSquare [7,5,2,2,2,1,1] [7,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg742

lemma sg7944 : RowSquare [7,5,2,2,2,1,1] [7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg4803

lemma sg7945 : RowSquare [7,5,2,2,2,1,1] [7,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg3200

lemma sg7946 : RowSquare [7,5,2,2,2,1,1] [7,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg116 sg2121

lemma sg7947 : RowSquare [7,5,2,2,2,1,1] [7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg842 sg735

lemma sg7948 : RowSquare [7,5,2,2,2,1,1] [7,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg839 sg742

lemma sg7949 : RowSquare [7,5,2,2,2,1,1] [7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg842 sg736

lemma sg7950 : RowSquare [7,5,2,2,2,1,1] [7,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg538 sg1150

lemma sg7951 : RowSquare [7,5,2,2,2,1,1] [7,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg3943

lemma sg7952 : RowSquare [7,5,2,2,2,1,1] [7,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg3204

lemma sg7953 : RowSquare [7,5,2,2,2,1,1] [7,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg116 sg2122

lemma sg7954 : RowSquare [7,5,2,2,2,1,1] [7,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg743

lemma sg7955 : RowSquare [7,5,2,2,2,1,1] [7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg535 sg1158

lemma sg7956 : RowSquare [7,5,2,2,2,1,1] [7,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg114 sg2126

lemma sg7957 : RowSquare [7,5,2,2,2,1,1] [7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg744

lemma sg7958 : RowSquare [7,5,2,2,2,1,1] [7,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg839 sg743

lemma sg7959 : RowSquare [7,5,2,2,2,1,1] [7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg843 sg736

lemma sg7960 : RowSquare [7,5,2,2,2,1,1] [7,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg842 sg739

lemma sg7961 : RowSquare [7,5,2,2,2,1,1] [7,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg3202

lemma sg7962 : RowSquare [7,5,2,2,2,1,1] [7,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg115 sg2126

lemma sg7963 : RowSquare [7,5,2,2,2,1,1] [7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg745

lemma sg7964 : RowSquare [7,5,2,2,2,1,1] [7,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg843 sg737

lemma sg7965 : RowSquare [7,5,2,2,2,1,1] [7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg746

lemma sg7966 : RowSquare [7,5,2,2,2,1,1] [7,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg118 sg2122

lemma sg7967 : RowSquare [7,5,2,2,2,1,1] [7,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg747

lemma sg7968 : RowSquare [7,5,2,2,2,1,1] [7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg748

lemma sg7969 : RowSquare [7,5,2,2,2,1,1] [8,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4801

lemma sg7970 : RowSquare [7,5,2,2,2,1,1] [8,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg3942

lemma sg7971 : RowSquare [7,5,2,2,2,1,1] [8,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg3944

lemma sg7972 : RowSquare [7,5,2,2,2,1,1] [8,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg3205

lemma sg7973 : RowSquare [7,5,2,2,2,1,1] [8,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg4802

lemma sg7974 : RowSquare [7,5,2,2,2,1,1] [8,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg842 sg742

lemma sg7975 : RowSquare [7,5,2,2,2,1,1] [8,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg3944

lemma sg7976 : RowSquare [7,5,2,2,2,1,1] [8,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg3205

lemma sg7977 : RowSquare [7,5,2,2,2,1,1] [8,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg116 sg2126

lemma sg7978 : RowSquare [7,5,2,2,2,1,1] [8,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg749

lemma sg7979 : RowSquare [7,5,2,2,2,1,1] [8,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg114 sg2132

lemma sg7980 : RowSquare [7,5,2,2,2,1,1] [8,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg842 sg744

lemma sg7981 : RowSquare [7,5,2,2,2,1,1] [8,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg3204

lemma sg7982 : RowSquare [7,5,2,2,2,1,1] [8,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg115 sg2132

lemma sg7983 : RowSquare [7,5,2,2,2,1,1] [8,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg750

lemma sg7984 : RowSquare [7,5,2,2,2,1,1] [8,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg118 sg2126

lemma sg7985 : RowSquare [7,5,2,2,2,1,1] [9,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg3942

lemma sg7986 : RowSquare [7,5,2,2,2,1,1] [9,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg3944

lemma sg7987 : RowSquare [7,5,2,2,2,1,1] [9,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg3205

lemma sg7988 : RowSquare [7,5,2,2,2,1,1] [9,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg116 sg2132

lemma sg7989 : RowSquare [7,5,2,2,2,1,1] [9,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg3205

lemma sg7990 : RowSquare [7,5,2,2,2,1,1] [9,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg117 sg2132

lemma sg7991 : RowSquare [7,5,2,2,2,1,1] [10,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg21 sg3349

lemma sg7992 : RowSquare [7,5,2,2,2,1,1] [10,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg3205

lemma sg7993 : RowSquare [7,6,2,1,1,1,1,1] [3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg74 sg2546

lemma sg7994 : RowSquare [7,6,2,1,1,1,1,1] [4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg2547

lemma sg7995 : RowSquare [8,3,2,2,2,2,1] [3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg74 sg2546

lemma sg7996 : RowSquare [8,3,2,2,2,2,1] [4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg2547

lemma sg7997 : RowSquare [8,3,2,2,2,2,1] [5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg2550

lemma sg7999 : RowSquare [9,3,2,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1113 sg720

lemma sg8000 : RowSquare [9,3,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg1620

lemma sg8001 : RowSquare [9,4,3,2,2] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg792

lemma sg8002 : RowSquare [9,4,4,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg350 sg1675

lemma sg8003 : RowSquare [9,4,4,3] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg942 sg833

lemma sg8004 : RowSquare [9,4,4,3] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg942 sg834

lemma sg8005 : RowSquare [9,4,4,3] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg943 sg834

lemma sg8006 : RowSquare [9,5,4,1,1] [3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg875

lemma sg8007 : RowSquare [9,7,4] [3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg306 sg1844

lemma sg8009 : RowSquare [10,2,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg2037

lemma sg8010 : RowSquare [10,2,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg2575

lemma sg8011 : RowSquare [10,3,3,2,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg942 sg891

lemma sg8012 : RowSquare [10,3,3,3,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg833 sg1000

lemma sg8013 : RowSquare [10,3,3,3,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg834 sg1001

lemma sg8014 : RowSquare [10,3,3,3,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg373 sg1677

lemma sg8015 : RowSquare [10,4,3,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg390 sg1675

lemma sg8016 : RowSquare [11,3,2,2,2] [4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg913

lemma sg8017 : RowSquare [11,3,2,2,2] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1000 sg915

lemma sg8018 : RowSquare [11,3,2,2,2] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg915

lemma sg8019 : RowSquare [3,2,2,2,2,2,2,2,2,1,1] [5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg644 sg1868

lemma sg8020 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1061 sg1575

lemma sg8021 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1104 sg1562

lemma sg8022 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,4] := by
  exact rowSquare_join (by decide) sg1105 sg1562

lemma sg8023 : RowSquare [3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] [9,6,2,2,2] := by
  exact rowSquare_join (by decide) sg1061 sg1576

lemma sg8024 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg1068 sg1538

lemma sg8025 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1068 sg1539

lemma sg8026 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1061 sg1548

lemma sg8027 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg1069 sg1539

lemma sg8028 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,5,5,5] := by
  exact rowSquare_join (by decide) sg693 sg1926

lemma sg8029 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1070 sg1538

lemma sg8030 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,4,3,2] := by
  exact rowSquare_join (by decide) sg1061 sg1549

lemma sg8031 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,4,4,1] := by
  exact rowSquare_join (by decide) sg644 sg1980

lemma sg8032 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg1061 sg1550

lemma sg8033 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg1071 sg1539

lemma sg8034 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,5,4] := by
  exact rowSquare_join (by decide) sg1072 sg1539

lemma sg8035 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg643 sg1982

lemma sg8036 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,6,2,1] := by
  exact rowSquare_join (by decide) sg1075 sg1534

lemma sg8037 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [6,6,6,3] := by
  exact rowSquare_join (by decide) sg1073 sg1539

lemma sg8038 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1068 sg1540

lemma sg8039 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg981 sg1561

lemma sg8040 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,4,4,3,3] := by
  exact rowSquare_join (by decide) sg982 sg1561

lemma sg8041 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg981 sg1562

lemma sg8042 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,4,4,4,2] := by
  exact rowSquare_join (by decide) sg982 sg1562

lemma sg8043 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1068 sg1542

lemma sg8044 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg981 sg1563

lemma sg8045 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,5,3,3,3] := by
  exact rowSquare_join (by decide) sg982 sg1563

lemma sg8046 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1068 sg1543

lemma sg8047 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,5,4,3,2] := by
  exact rowSquare_join (by decide) sg982 sg1564

lemma sg8048 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,5,4,4,1] := by
  exact rowSquare_join (by decide) sg1069 sg1544

lemma sg8049 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg975 sg1570

lemma sg8050 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg981 sg1565

lemma sg8051 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1070 sg1542

lemma sg8052 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1068 sg1545

lemma sg8053 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg981 sg1566

lemma sg8054 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,6,3,3,2] := by
  exact rowSquare_join (by decide) sg982 sg1566

lemma sg8055 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg975 sg1571

lemma sg8056 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg981 sg1567

lemma sg8057 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1068 sg1546

lemma sg8058 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,7,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1070 sg1545

lemma sg8059 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,7,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg975 sg1572

lemma sg8060 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,7,3,2,1,1] := by
  exact rowSquare_join (by decide) sg976 sg1572

lemma sg8061 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,7,3,2,2] := by
  exact rowSquare_join (by decide) sg1061 sg1551

lemma sg8062 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [7,7,3,3,1] := by
  exact rowSquare_join (by decide) sg1072 sg1545

lemma sg8063 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg981 sg1568

lemma sg8064 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1111 sg1461

lemma sg8065 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1068 sg1547

lemma sg8066 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg981 sg1569

lemma sg8067 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,4,3,3,3] := by
  exact rowSquare_join (by decide) sg982 sg1569

lemma sg8068 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg978 sg1570

lemma sg8069 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1070 sg1547

lemma sg8070 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg978 sg1571

lemma sg8071 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg978 sg1572

lemma sg8072 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg975 sg1573

lemma sg8073 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,7,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg975 sg1574

lemma sg8074 : RowSquare [3,3,2,2,2,2,1,1,1,1,1,1,1] [8,8,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg577 sg2011

lemma sg8075 : RowSquare [3,3,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg390 sg2433

lemma sg8076 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg1538

lemma sg8077 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg1033 sg1539

lemma sg8078 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1068 sg1519

lemma sg8079 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1105 sg1417

lemma sg8080 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1033 sg1541

lemma sg8081 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1069 sg1520

lemma sg8082 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1070 sg1519

lemma sg8083 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1068 sg1521

lemma sg8084 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg1543

lemma sg8085 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1033 sg1544

lemma sg8086 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,5,5,5] := by
  exact rowSquare_join (by decide) sg693 sg1908

lemma sg8087 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1070 sg1520

lemma sg8088 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1070 sg1521

lemma sg8089 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1072 sg1520

lemma sg8090 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg1545

lemma sg8091 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1034 sg1540

lemma sg8092 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1034 sg1541

lemma sg8093 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1092 sg1460

lemma sg8094 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1092 sg1461

lemma sg8095 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1034 sg1542

lemma sg8096 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg1547

lemma sg8097 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1035 sg1541

lemma sg8098 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg981 sg1553

lemma sg8099 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1074 sg1519

lemma sg8100 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1035 sg1542

lemma sg8101 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1035 sg1544

lemma sg8102 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1035 sg1545

lemma sg8103 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [7,7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1109 sg1422

lemma sg8104 : RowSquare [4,3,2,2,2,1,1,1,1,1,1,1,1] [8,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1092 sg1466

lemma sg8105 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1092 sg1552

lemma sg8106 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1092 sg1553

lemma sg8107 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1092 sg1554

lemma sg8108 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1092 sg1555

lemma sg8109 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1093 sg1553

lemma sg8110 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1093 sg1554

lemma sg8111 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1093 sg1555

lemma sg8112 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1094 sg1554

lemma sg8113 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1094 sg1555

lemma sg8114 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,4,4,4] := by
  exact rowSquare_join (by decide) sg1095 sg1555

lemma sg8115 : RowSquare [4,4,2,2,2,2,2,2,1] [5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg879 sg1304

lemma sg8116 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg1891

lemma sg8117 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg370 sg2311

lemma sg8118 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg2391

lemma sg8119 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2392

lemma sg8120 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg614 sg1891

lemma sg8121 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg371 sg2311

lemma sg8122 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg2393

lemma sg8123 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg3006

lemma sg8124 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2394

lemma sg8125 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg615 sg1891

lemma sg8126 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg2395

lemma sg8127 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg373 sg2311

lemma sg8128 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg616 sg1891

lemma sg8129 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg1892

lemma sg8130 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1893

lemma sg8131 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg617 sg1891

lemma sg8132 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg370 sg2314

lemma sg8133 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg940 sg1517

lemma sg8134 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1518

lemma sg8135 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg1892

lemma sg8136 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1519

end UniversalTensorSquare
end
end

end OAI
