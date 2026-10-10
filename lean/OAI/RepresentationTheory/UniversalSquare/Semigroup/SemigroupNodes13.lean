import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes10

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5728 : RowSquare [6,5,2,2,2,1] [8,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg243 sg842

lemma sg5729 : RowSquare [6,5,2,2,2,1] [9,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg2543

lemma sg5730 : RowSquare [6,5,2,2,2,1] [9,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg3248

lemma sg5731 : RowSquare [6,5,3,2,1,1] [3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg1616

lemma sg5732 : RowSquare [6,6,1,1,1,1,1,1] [3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg2546

lemma sg5733 : RowSquare [7,5,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg21 sg2251

lemma sg5734 : RowSquare [7,5,3,1,1,1] [4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg306 sg810

lemma sg5736 : RowSquare [8,3,2,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg705 sg431

lemma sg5737 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg703 sg430

lemma sg5738 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg703 sg429

lemma sg5739 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg733

lemma sg5740 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg223 sg1141

lemma sg5741 : RowSquare [8,3,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg1625

lemma sg5742 : RowSquare [8,3,2,1,1,1,1,1] [3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg220 sg1140

lemma sg5743 : RowSquare [8,3,2,1,1,1,1,1] [3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg89 sg1624

lemma sg5744 : RowSquare [8,3,2,1,1,1,1,1] [3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg89 sg1623

lemma sg5745 : RowSquare [8,3,2,1,1,1,1,1] [3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg220 sg1138

lemma sg5746 : RowSquare [8,3,2,1,1,1,1,1] [3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg89 sg1621

lemma sg5747 : RowSquare [8,3,2,1,1,1,1,1] [4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg88 sg1623

lemma sg5748 : RowSquare [8,3,2,1,1,1,1,1] [5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg1622

lemma sg5749 : RowSquare [8,3,3,1,1,1,1] [3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg2120

lemma sg5750 : RowSquare [8,4,2,1,1,1,1] [4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg2123

lemma sg5751 : RowSquare [8,4,3,1,1,1] [4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg306 sg893

lemma sg5752 : RowSquare [8,4,3,2,1] [4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg513

lemma sg5753 : RowSquare [8,4,3,3] [4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg835

lemma sg5754 : RowSquare [8,5,3,1,1] [3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg306 sg912

lemma sg5755 : RowSquare [8,5,3,1,1] [3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg1688

lemma sg5756 : RowSquare [8,7,2,1] [3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg849

lemma sg5758 : RowSquare [9,2,1,1,1,1,1,1,1] [2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg425 sg719

lemma sg5759 : RowSquare [9,2,1,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg1136

lemma sg5760 : RowSquare [9,2,1,1,1,1,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg1620

lemma sg5761 : RowSquare [9,2,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg2114

lemma sg5762 : RowSquare [9,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg2618

lemma sg5763 : RowSquare [9,3,2,2,1,1] [4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg142 sg1332

lemma sg5764 : RowSquare [9,3,3,1,1,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg349 sg892

lemma sg5765 : RowSquare [9,3,3,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg350 sg892

lemma sg5766 : RowSquare [9,3,3,2,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg373 sg828

lemma sg5767 : RowSquare [9,3,3,2,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg551 sg590

lemma sg5768 : RowSquare [9,4,2,1,1,1] [2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg1754

lemma sg5769 : RowSquare [9,4,2,1,1,1] [4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg357 sg889

lemma sg5770 : RowSquare [9,4,2,1,1,1] [4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg356 sg892

lemma sg5771 : RowSquare [9,4,2,1,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg390 sg808

lemma sg5772 : RowSquare [9,4,3,2] [3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg943

lemma sg5773 : RowSquare [9,4,3,2] [4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg371 sg853

lemma sg5774 : RowSquare [9,4,3,2] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg550

lemma sg5775 : RowSquare [9,4,3,2] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg616 sg551

lemma sg5776 : RowSquare [10,2,2,2,2] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg586

lemma sg5777 : RowSquare [10,3,2,1,1,1] [4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg195 sg1330

lemma sg5778 : RowSquare [10,3,2,2,1] [3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg998

lemma sg5779 : RowSquare [10,3,2,2,1] [3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg616

lemma sg5780 : RowSquare [10,3,2,2,1] [3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1000

lemma sg5781 : RowSquare [10,3,2,2,1] [4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg371 sg914

lemma sg5782 : RowSquare [10,3,2,2,1] [4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg371 sg915

lemma sg5783 : RowSquare [10,3,2,2,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg589

lemma sg5784 : RowSquare [10,3,2,2,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg372 sg915

lemma sg5785 : RowSquare [10,3,2,2,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg373 sg914

lemma sg5786 : RowSquare [10,3,2,2,1] [5,5,4,4] := by
  exact rowSquare_join (by decide) sg373 sg922

lemma sg5787 : RowSquare [10,3,3,1,1] [4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg348 sg1000

lemma sg5788 : RowSquare [10,3,3,1,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg636 sg589

lemma sg5789 : RowSquare [10,3,3,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg350 sg1000

lemma sg5790 : RowSquare [10,4,2,2] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg615

lemma sg5791 : RowSquare [10,4,3,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg636 sg615

lemma sg5792 : RowSquare [11,3,2,2] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg372 sg1033

lemma sg5793 : RowSquare [11,3,2,2] [5,5,4,4] := by
  exact rowSquare_join (by decide) sg373 sg1040

lemma sg5794 : RowSquare [3,3,3,2,1,1,1,1,1,1,1,1] [5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg692 sg1061

lemma sg5795 : RowSquare [3,3,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg693 sg1061

lemma sg5796 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg692 sg1031

lemma sg5797 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg693 sg1031

lemma sg5798 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg692 sg1032

lemma sg5799 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg692 sg1033

lemma sg5800 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg693 sg1032

lemma sg5801 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg693 sg1033

lemma sg5802 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg1520

lemma sg5803 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg694 sg1032

lemma sg5804 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg694 sg1033

lemma sg5805 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg1068

lemma sg5806 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg1069

lemma sg5807 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg697 sg1032

lemma sg5808 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg697 sg1033

lemma sg5809 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg1070

lemma sg5810 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1104

lemma sg5811 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg643 sg1093

lemma sg5812 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1105

lemma sg5813 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg674 sg1069

lemma sg5814 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg698 sg1033

lemma sg5815 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg643 sg1094

lemma sg5816 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg644 sg1095

lemma sg5817 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1106

lemma sg5818 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg674 sg1070

lemma sg5819 : RowSquare [4,3,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg694 sg1038

lemma sg5820 : RowSquare [4,3,3,2,1,1,1,1,1,1,1] [5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg374 sg1455

lemma sg5821 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg673 sg1092

lemma sg5822 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg1093

lemma sg5823 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg1094

lemma sg5824 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg1095

lemma sg5825 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg674 sg1093

lemma sg5826 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg1094

lemma sg5827 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1095

lemma sg5828 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2] := by
  exact rowSquare_join (by decide) sg675 sg1094

lemma sg5829 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,1] := by
  exact rowSquare_join (by decide) sg675 sg1095

lemma sg5830 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1,1] [7,4,4,4] := by
  exact rowSquare_join (by decide) sg676 sg1095

lemma sg5831 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg673 sg1031

lemma sg5832 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg1032

lemma sg5833 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg673 sg1033

lemma sg5834 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg1520

lemma sg5835 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg1031

lemma sg5836 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg674 sg1032

lemma sg5837 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg674 sg1033

lemma sg5838 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg675 sg1031

lemma sg5839 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg676 sg1031

lemma sg5840 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg675 sg1032

lemma sg5841 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg675 sg1033

lemma sg5842 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg676 sg1032

lemma sg5843 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg676 sg1033

lemma sg5844 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg1520

lemma sg5845 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg372 sg1520

lemma sg5846 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg1521

lemma sg5847 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1520

lemma sg5848 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg1522

lemma sg5849 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1523

lemma sg5850 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg372 sg1522

lemma sg5851 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg372 sg1523

lemma sg5852 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [5,5,5,4] := by
  exact rowSquare_join (by decide) sg373 sg1523

lemma sg5853 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg1092

lemma sg5854 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1093

lemma sg5855 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg1092

lemma sg5856 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1094

lemma sg5857 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg1036

lemma sg5858 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1095

lemma sg5859 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg677 sg1032

lemma sg5860 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg677 sg1033

lemma sg5861 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg614 sg1093

lemma sg5862 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1094

lemma sg5863 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1093

lemma sg5864 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg678 sg1033

lemma sg5865 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg1094

lemma sg5866 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg1527

lemma sg5867 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg674 sg1038

lemma sg5868 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg1039

lemma sg5869 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1040

lemma sg5870 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg681 sg1031

lemma sg5871 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1041

lemma sg5872 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg675 sg1039

lemma sg5873 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg675 sg1040

lemma sg5874 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,4,4] := by
  exact rowSquare_join (by decide) sg676 sg1040

lemma sg5875 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg377 sg1520

lemma sg5876 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg1527

lemma sg5877 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg378 sg1520

lemma sg5878 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1528

lemma sg5879 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg372 sg1527

lemma sg5880 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg373 sg1527

lemma sg5881 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1529

lemma sg5882 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,4,2,1] := by
  exact rowSquare_join (by decide) sg372 sg1528

lemma sg5883 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,4,3] := by
  exact rowSquare_join (by decide) sg373 sg1528

lemma sg5884 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg372 sg1529

lemma sg5885 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,6,5,2] := by
  exact rowSquare_join (by decide) sg373 sg1529

lemma sg5886 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1096

lemma sg5887 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3] := by
  exact rowSquare_join (by decide) sg682 sg1033

lemma sg5888 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [7,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1048

lemma sg5889 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg1520

lemma sg5890 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg1031

lemma sg5891 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1032

lemma sg5892 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg1417

lemma sg5893 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1033

lemma sg5894 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1522

lemma sg5895 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg1031

lemma sg5896 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1523

lemma sg5897 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg616 sg1031

lemma sg5898 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1032

lemma sg5899 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg615 sg1033

lemma sg5900 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1417

lemma sg5901 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg616 sg1032

lemma sg5902 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg616 sg1033

lemma sg5903 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg613 sg1034

lemma sg5904 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1036

lemma sg5905 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg673 sg959

lemma sg5906 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1037

lemma sg5907 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg960

lemma sg5908 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg673 sg961

lemma sg5909 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1041

lemma sg5910 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1036

lemma sg5911 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg675 sg961

lemma sg5912 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1527

lemma sg5913 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg614 sg1038

lemma sg5914 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg623 sg1031

lemma sg5915 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1045

lemma sg5916 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg677 sg961

lemma sg5917 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg1044

lemma sg5918 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg674 sg964

lemma sg5919 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1048

lemma sg5920 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg621 sg1038

lemma sg5921 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [7,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1050

lemma sg5922 : RowSquare [4,4,2,2,1,1,1,1,1,1,1] [7,3,3,3,3] := by
  exact rowSquare_join (by decide) sg682 sg961

lemma sg5923 : RowSquare [4,4,2,2,2,2,2,1] [4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg1650

lemma sg5924 : RowSquare [4,4,2,2,2,2,2,1] [4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg1650

lemma sg5925 : RowSquare [4,4,2,2,2,2,2,1] [4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg561 sg877

lemma sg5926 : RowSquare [4,4,2,2,2,2,2,1] [4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg561 sg879

lemma sg5927 : RowSquare [4,4,2,2,2,2,2,1] [4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg1650

lemma sg5928 : RowSquare [4,4,2,2,2,2,2,1] [5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg211 sg1650

lemma sg5929 : RowSquare [4,4,2,2,2,2,2,1] [5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg561 sg880

lemma sg5930 : RowSquare [4,4,2,2,2,2,2,1] [5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg212 sg1650

lemma sg5931 : RowSquare [4,4,2,2,2,2,2,1] [5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg1651

lemma sg5932 : RowSquare [4,4,2,2,2,2,2,1] [5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg1651

lemma sg5933 : RowSquare [4,4,2,2,2,2,2,1] [5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg561 sg882

lemma sg5934 : RowSquare [4,4,2,2,2,2,2,1] [5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg1650

lemma sg5935 : RowSquare [4,4,2,2,2,2,2,1] [5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg1651

lemma sg5936 : RowSquare [4,4,2,2,2,2,2,1] [5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg1652

lemma sg5937 : RowSquare [4,4,2,2,2,2,2,1] [5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg1652

lemma sg5938 : RowSquare [4,4,2,2,2,2,2,1] [5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg1652

lemma sg5939 : RowSquare [4,4,2,2,2,2,2,1] [6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg1650

lemma sg5940 : RowSquare [4,4,2,2,2,2,2,1] [6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg211 sg1651

lemma sg5941 : RowSquare [4,4,2,2,2,2,2,1] [6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg1650

lemma sg5942 : RowSquare [4,4,2,2,2,2,2,1] [6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg212 sg1651

lemma sg5943 : RowSquare [4,4,2,2,2,2,2,1] [6,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg1655

lemma sg5944 : RowSquare [4,4,2,2,2,2,2,1] [6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg209 sg1655

lemma sg5945 : RowSquare [4,4,2,2,2,2,2,1] [6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg1651

lemma sg5946 : RowSquare [4,4,2,2,2,2,2,1] [6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg210 sg1655

lemma sg5947 : RowSquare [4,4,2,2,2,2,2,1] [6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg1652

lemma sg5948 : RowSquare [4,4,2,2,2,2,2,1] [7,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg1650

lemma sg5949 : RowSquare [4,4,2,2,2,2,2,1] [7,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg214 sg1651

lemma sg5950 : RowSquare [4,4,2,2,2,2,2,1] [7,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg211 sg1655

lemma sg5951 : RowSquare [4,4,2,2,2,2,2,1] [7,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg215 sg1651

lemma sg5952 : RowSquare [4,4,2,2,2,2,2,1] [7,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg212 sg1655

lemma sg5953 : RowSquare [4,4,2,2,2,2,2,1] [7,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg213 sg1655

lemma sg5954 : RowSquare [4,4,2,2,2,2,2,1] [8,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg217 sg1650

lemma sg5955 : RowSquare [4,4,2,2,2,2,2,1] [8,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg216 sg1651

lemma sg5956 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg673 sg849

lemma sg5957 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg849

lemma sg5958 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg675 sg849

lemma sg5959 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg676 sg849

lemma sg5960 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg178 sg1796

lemma sg5961 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg615 sg940

lemma sg5962 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg941

lemma sg5963 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg616 sg940

lemma sg5964 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg614 sg943

lemma sg5965 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1413

lemma sg5966 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg941

lemma sg5967 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg616 sg941

lemma sg5968 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg615 sg942

lemma sg5969 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg615 sg943

lemma sg5970 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg616 sg942

lemma sg5971 : RowSquare [4,4,3,2,1,1,1,1,1,1] [4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg616 sg943

lemma sg5972 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg677 sg849

lemma sg5973 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg850

lemma sg5974 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg613 sg944

lemma sg5975 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg678 sg849

lemma sg5976 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg850

lemma sg5977 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg945

lemma sg5978 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg679 sg849

lemma sg5979 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg946

lemma sg5980 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg676 sg850

lemma sg5981 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg853

lemma sg5982 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg179 sg1796

lemma sg5983 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg680 sg849

lemma sg5984 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg948

lemma sg5985 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg681 sg849

lemma sg5986 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg950

lemma sg5987 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg947

lemma sg5988 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg674 sg853

lemma sg5989 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg951

lemma sg5990 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg946

lemma sg5991 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg693 sg832

lemma sg5992 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg693 sg833

lemma sg5993 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg616 sg947

lemma sg5994 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg622 sg940

lemma sg5995 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg948

lemma sg5996 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg614 sg950

lemma sg5997 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg623 sg940

lemma sg5998 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg614 sg951

lemma sg5999 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg615 sg950

lemma sg6000 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg616 sg949

lemma sg6001 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg616 sg950

lemma sg6002 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg696 sg832

lemma sg6003 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg615 sg951

lemma sg6004 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg696 sg834

lemma sg6005 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg616 sg951

lemma sg6006 : RowSquare [4,4,3,2,1,1,1,1,1,1] [5,5,5,4] := by
  exact rowSquare_join (by decide) sg373 sg1294

lemma sg6007 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg682 sg849

lemma sg6008 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg952

lemma sg6009 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg952

lemma sg6010 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg955

lemma sg6011 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg673 sg858

lemma sg6012 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg614 sg955

lemma sg6013 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1 sg4575

lemma sg6014 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg674 sg859

lemma sg6015 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,5,4,4] := by
  exact rowSquare_join (by decide) sg693 sg837

lemma sg6016 : RowSquare [4,4,3,2,1,1,1,1,1,1] [6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg694 sg836

lemma sg6017 : RowSquare [5,3,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1109

lemma sg6018 : RowSquare [5,3,2,1,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg696 sg998

lemma sg6019 : RowSquare [5,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg696 sg999

lemma sg6020 : RowSquare [5,3,2,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1112

lemma sg6021 : RowSquare [5,3,2,2,1,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg695 sg910

lemma sg6022 : RowSquare [5,3,2,2,1,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg696 sg910

lemma sg6023 : RowSquare [5,3,3,2,1,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg2137

lemma sg6024 : RowSquare [5,3,3,2,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg218 sg1683

lemma sg6025 : RowSquare [5,3,3,2,1,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg2137

lemma sg6026 : RowSquare [5,3,3,2,1,1,1,1,1,1] [5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg219 sg1683

lemma sg6027 : RowSquare [5,3,3,2,1,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg106 sg2137

lemma sg6028 : RowSquare [5,3,3,2,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg221 sg1683

lemma sg6029 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1092

lemma sg6030 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg998

lemma sg6031 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1094

lemma sg6032 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg673 sg999

lemma sg6033 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1095

lemma sg6034 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg673 sg1000

lemma sg6035 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg673 sg1001

lemma sg6036 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg998

lemma sg6037 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg675 sg998

lemma sg6038 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg999

lemma sg6039 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg676 sg998

lemma sg6040 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg675 sg999

lemma sg6041 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg676 sg999

lemma sg6042 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg675 sg1000

lemma sg6043 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg675 sg1001

lemma sg6044 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg676 sg1000

lemma sg6045 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg676 sg1001

lemma sg6046 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1096

lemma sg6047 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg1092

lemma sg6048 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1093

lemma sg6049 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg677 sg1000

lemma sg6050 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg677 sg1001

lemma sg6051 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1100

lemma sg6052 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg589 sg1094

lemma sg6053 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg590 sg1095

lemma sg6054 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg681 sg998

lemma sg6055 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg680 sg999

lemma sg6056 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg674 sg1007

lemma sg6057 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1008

lemma sg6058 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,2] := by
  exact rowSquare_join (by decide) sg680 sg1001

lemma sg6059 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg681 sg999

lemma sg6060 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg681 sg1000

lemma sg6061 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg675 sg1007

lemma sg6062 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg675 sg1008

lemma sg6063 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [6,5,4,4] := by
  exact rowSquare_join (by decide) sg676 sg1008

lemma sg6064 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1101

lemma sg6065 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1096

lemma sg6066 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1097

lemma sg6067 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1102

lemma sg6068 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1096

lemma sg6069 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,3,3,3,3] := by
  exact rowSquare_join (by decide) sg682 sg1001

lemma sg6070 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1100

lemma sg6071 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg684 sg999

lemma sg6072 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1103

lemma sg6073 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1100

lemma sg6074 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg686 sg998

lemma sg6075 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg686 sg999

lemma sg6076 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1015

lemma sg6077 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2] := by
  exact rowSquare_join (by decide) sg686 sg1001

lemma sg6078 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1016

lemma sg6079 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,1] := by
  exact rowSquare_join (by decide) sg675 sg1015

lemma sg6080 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1] [7,6,3,3] := by
  exact rowSquare_join (by decide) sg676 sg1015

lemma sg6081 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg613 sg998

lemma sg6082 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg999

lemma sg6083 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1000

lemma sg6084 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1001

lemma sg6085 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg614 sg998

lemma sg6086 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg615 sg998

lemma sg6087 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg999

lemma sg6088 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg616 sg998

lemma sg6089 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg614 sg1000

lemma sg6090 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1001

lemma sg6091 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1041

lemma sg6092 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg999

lemma sg6093 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg616 sg999

lemma sg6094 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1000

lemma sg6095 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg615 sg1001

lemma sg6096 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg616 sg1000

lemma sg6097 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg616 sg1001

lemma sg6098 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg613 sg1002

lemma sg6099 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg1003

lemma sg6100 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1004

lemma sg6101 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1005

lemma sg6102 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1006

lemma sg6103 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg681 sg910

lemma sg6104 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1005

lemma sg6105 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1041

lemma sg6106 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1004

lemma sg6107 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg621 sg998

lemma sg6108 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg614 sg1006

lemma sg6109 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg622 sg998

lemma sg6110 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1006

lemma sg6111 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1008

lemma sg6112 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg616 sg1006

lemma sg6113 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg621 sg1001

lemma sg6114 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg623 sg998

lemma sg6115 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg616 sg1008

lemma sg6116 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg685 sg910

lemma sg6117 : RowSquare [5,4,2,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg686 sg910

lemma sg6118 : RowSquare [5,4,2,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg910

lemma sg6119 : RowSquare [5,4,2,2,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg623 sg910

lemma sg6120 : RowSquare [5,4,2,2,1,1,1,1,1,1] [4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1378

lemma sg6121 : RowSquare [5,4,2,2,1,1,1,1,1,1] [4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1379

lemma sg6122 : RowSquare [5,4,2,2,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg628 sg910

lemma sg6123 : RowSquare [5,4,2,2,1,1,1,1,1,1] [5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg623 sg913

lemma sg6124 : RowSquare [5,4,2,2,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg2596

lemma sg6125 : RowSquare [5,4,2,2,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg2597

lemma sg6126 : RowSquare [5,4,2,2,2,2,1,1] [4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg2596

lemma sg6127 : RowSquare [5,4,2,2,2,2,1,1] [4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg2597

lemma sg6128 : RowSquare [5,4,2,2,2,2,1,1] [4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg2596

lemma sg6129 : RowSquare [5,4,2,2,2,2,1,1] [4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg2597

end UniversalTensorSquare
end
end

end OAI
