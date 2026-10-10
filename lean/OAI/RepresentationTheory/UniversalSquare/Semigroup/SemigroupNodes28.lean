import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes27

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11740 : RowSquare [6,6,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg1757

lemma sg11741 : RowSquare [6,6,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg1758

lemma sg11742 : RowSquare [7,5,2,2,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg2702

lemma sg11743 : RowSquare [7,5,3,2,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg321 sg4160

lemma sg11744 : RowSquare [7,5,3,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg316 sg4161

lemma sg11745 : RowSquare [7,5,3,2,1,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg4160

lemma sg11746 : RowSquare [7,5,3,2,1,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg327 sg4160

lemma sg11747 : RowSquare [7,5,3,2,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg4161

lemma sg11748 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg2251

lemma sg11749 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg2251

lemma sg11750 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1327 sg2252

lemma sg11751 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg2251

lemma sg11752 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1327 sg2253

lemma sg11753 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg2251

lemma sg11754 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg2251

lemma sg11755 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1332 sg2251

lemma sg11756 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg2252

lemma sg11757 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1257 sg2251

lemma sg11758 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg893 sg2702

lemma sg11759 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg894 sg2702

lemma sg11760 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg895 sg2702

lemma sg11761 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg896 sg2702

lemma sg11762 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg897 sg2702

lemma sg11763 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg898 sg2702

lemma sg11764 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1261 sg2251

lemma sg11765 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg899 sg2702

lemma sg11766 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1262 sg2251

lemma sg11767 : RowSquare [7,6,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1263 sg2251

lemma sg11768 : RowSquare [7,6,2,2,2,2,2,1] [5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10875

lemma sg11769 : RowSquare [7,6,2,2,2,2,2,1] [5,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10876

lemma sg11770 : RowSquare [7,6,2,2,2,2,2,1] [5,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10877

lemma sg11771 : RowSquare [7,6,2,2,2,2,2,1] [5,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10878

lemma sg11772 : RowSquare [7,6,2,2,2,2,2,1] [5,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10879

lemma sg11773 : RowSquare [7,6,2,2,2,2,2,1] [5,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg10880

lemma sg11774 : RowSquare [7,6,2,2,2,2,2,1] [5,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10882

lemma sg11775 : RowSquare [7,6,2,2,2,2,2,1] [5,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10883

lemma sg11776 : RowSquare [7,6,2,2,2,2,2,1] [5,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10884

lemma sg11777 : RowSquare [7,6,2,2,2,2,2,1] [5,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg10885

lemma sg11778 : RowSquare [7,6,2,2,2,2,2,1] [5,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10886

lemma sg11779 : RowSquare [7,6,2,2,2,2,2,1] [5,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10887

lemma sg11780 : RowSquare [7,6,2,2,2,2,2,1] [5,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg10888

lemma sg11781 : RowSquare [7,6,2,2,2,2,2,1] [6,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10899

lemma sg11782 : RowSquare [7,6,2,2,2,2,2,1] [6,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10900

lemma sg11783 : RowSquare [7,6,2,2,2,2,2,1] [6,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10901

lemma sg11784 : RowSquare [7,6,2,2,2,2,2,1] [6,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg10902

lemma sg11785 : RowSquare [7,6,2,2,2,2,2,1] [6,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10903

lemma sg11786 : RowSquare [7,6,3,2,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg263 sg4160

lemma sg11787 : RowSquare [7,6,3,2,1,1,1,1,1,1] [7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg266 sg4160

lemma sg11788 : RowSquare [7,7,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1245 sg2251

lemma sg11789 : RowSquare [7,7,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1246 sg2251

lemma sg11790 : RowSquare [7,7,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1247 sg2251

lemma sg11791 : RowSquare [7,7,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1248 sg2251

lemma sg11792 : RowSquare [7,7,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1249 sg2251

lemma sg11793 : RowSquare [7,7,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1250 sg2251

lemma sg11794 : RowSquare [7,7,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1251 sg2251

lemma sg11795 : RowSquare [7,7,2,2,2,2,2] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1176 sg2105

lemma sg11796 : RowSquare [7,7,2,2,2,2,2] [2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1169 sg2105

lemma sg11797 : RowSquare [7,7,2,2,2,2,2] [2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1169 sg2104

lemma sg11798 : RowSquare [7,7,2,2,2,2,2] [2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1169 sg2103

lemma sg11799 : RowSquare [7,7,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1169 sg2101

lemma sg11800 : RowSquare [7,7,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1169 sg2097

lemma sg11801 : RowSquare [7,7,2,2,2,2,2] [2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg367 sg3789

lemma sg11802 : RowSquare [7,7,2,2,2,2,2] [3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1173 sg2105

lemma sg11803 : RowSquare [7,7,2,2,2,2,2] [3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1164 sg2105

lemma sg11804 : RowSquare [7,7,2,2,2,2,2] [3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1164 sg2104

lemma sg11805 : RowSquare [7,7,2,2,2,2,2] [3,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1164 sg2102

lemma sg11806 : RowSquare [7,7,2,2,2,2,2] [3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1170 sg2105

lemma sg11807 : RowSquare [7,7,2,2,2,2,2] [3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1167 sg2105

lemma sg11808 : RowSquare [7,7,2,2,2,2,2] [3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1163 sg2104

lemma sg11809 : RowSquare [7,7,2,2,2,2,2] [3,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1163 sg2099

lemma sg11810 : RowSquare [7,7,2,2,2,2,2] [3,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1164 sg2092

lemma sg11811 : RowSquare [7,7,2,2,2,2,2] [3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg83 sg5293

lemma sg11812 : RowSquare [7,7,2,2,2,2,2] [4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1166 sg2105

lemma sg11813 : RowSquare [7,7,2,2,2,2,2] [4,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1156 sg2104

lemma sg11814 : RowSquare [7,7,2,2,2,2,2] [4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1160 sg2105

lemma sg11815 : RowSquare [7,7,2,2,2,2,2] [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1153 sg2103

lemma sg11816 : RowSquare [7,7,2,2,2,2,2] [5,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg2100

lemma sg11817 : RowSquare [7,7,2,2,2,2,2] [5,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg2098

lemma sg11818 : RowSquare [7,7,2,2,2,2,2] [5,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg2095

lemma sg11819 : RowSquare [7,7,2,2,2,2,2] [5,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1147 sg2091

lemma sg11820 : RowSquare [7,7,2,2,2,2,2] [5,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1150 sg2094

lemma sg11821 : RowSquare [7,7,2,2,2,2,2] [5,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg2094

lemma sg11822 : RowSquare [7,7,2,2,2,2,2] [5,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg2090

lemma sg11823 : RowSquare [7,7,2,2,2,2,2] [5,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1147 sg2089

lemma sg11824 : RowSquare [7,7,2,2,2,2,2] [5,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1150 sg2088

lemma sg11825 : RowSquare [7,7,2,2,2,2,2] [5,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg2087

lemma sg11826 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg517 sg3521

lemma sg11827 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg518 sg3521

lemma sg11828 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg519 sg3521

lemma sg11829 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg520 sg3521

lemma sg11830 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg521 sg3521

lemma sg11831 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg522 sg3521

lemma sg11832 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg523 sg3521

lemma sg11833 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg524 sg3521

lemma sg11834 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg525 sg3521

lemma sg11835 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg527 sg3521

lemma sg11836 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg528 sg3521

lemma sg11837 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [6,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg529 sg3521

lemma sg11838 : RowSquare [8,6,1,1,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg530 sg3521

lemma sg11839 : RowSquare [8,6,2,2,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg4345

lemma sg11840 : RowSquare [8,6,2,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg4345

lemma sg11841 : RowSquare [8,6,2,2,2,2,1,1] [4,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg807 sg2546

lemma sg11842 : RowSquare [8,6,2,2,2,2,1,1] [4,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg808 sg2546

lemma sg11843 : RowSquare [8,6,2,2,2,2,1,1] [4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg809 sg2546

lemma sg11844 : RowSquare [8,6,2,2,2,2,1,1] [4,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg656 sg3161

lemma sg11845 : RowSquare [8,6,2,2,2,2,1,1] [4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg364 sg3802

lemma sg11846 : RowSquare [8,6,2,2,2,2,1,1] [5,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg811 sg2546

lemma sg11847 : RowSquare [8,6,2,2,2,2,1,1] [5,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg807 sg2547

lemma sg11848 : RowSquare [8,6,2,2,2,2,1,1] [5,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg813 sg2546

lemma sg11849 : RowSquare [8,6,2,2,2,2,1,1] [5,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg808 sg2547

lemma sg11850 : RowSquare [8,6,2,2,2,2,1,1] [5,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg809 sg2547

lemma sg11851 : RowSquare [8,6,2,2,2,2,1,1] [5,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg364 sg3801

lemma sg11852 : RowSquare [8,6,2,2,2,2,1,1] [5,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg814 sg2546

lemma sg11853 : RowSquare [8,6,2,2,2,2,1,1] [5,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg807 sg2548

lemma sg11854 : RowSquare [8,6,2,2,2,2,1,1] [5,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1205 sg2058

lemma sg11855 : RowSquare [8,6,2,2,2,2,1,1] [5,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg816 sg2546

lemma sg11856 : RowSquare [8,6,2,2,2,2,1,1] [5,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg808 sg2548

lemma sg11857 : RowSquare [8,6,2,2,2,2,1,1] [5,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1208 sg2044

lemma sg11858 : RowSquare [8,6,2,2,2,2,1,1] [5,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg809 sg2548

lemma sg11859 : RowSquare [8,6,2,2,2,2,1,1] [5,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1207 sg2044

lemma sg11860 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg807 sg2549

lemma sg11861 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg8689

lemma sg11862 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg8690

lemma sg11863 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg808 sg2549

lemma sg11864 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg809 sg2549

lemma sg11865 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg1207 sg2043

lemma sg11866 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg762 sg2581

lemma sg11867 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7462

lemma sg11868 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg13 sg7463

lemma sg11869 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg13 sg7464

lemma sg11870 : RowSquare [8,6,2,2,2,2,1,1] [5,5,5,5,4] := by
  exact rowSquare_join (by decide) sg762 sg2582

lemma sg11871 : RowSquare [8,6,2,2,2,2,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10581

lemma sg11872 : RowSquare [8,6,2,2,2,2,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8682

lemma sg11873 : RowSquare [8,6,2,2,2,2,1,1] [6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8691

lemma sg11874 : RowSquare [8,6,2,2,2,2,1,1] [6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7465

lemma sg11875 : RowSquare [8,6,2,2,2,2,1,1] [6,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10582

lemma sg11876 : RowSquare [8,6,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10583

lemma sg11877 : RowSquare [8,6,2,2,2,2,1,1] [6,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10584

lemma sg11878 : RowSquare [8,6,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10585

lemma sg11879 : RowSquare [8,6,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10586

lemma sg11880 : RowSquare [8,6,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg10587

lemma sg11881 : RowSquare [8,6,2,2,2,2,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8683

lemma sg11882 : RowSquare [8,6,2,2,2,2,1,1] [6,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7256

lemma sg11883 : RowSquare [8,6,2,2,2,2,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11509

lemma sg11884 : RowSquare [8,6,2,2,2,2,1,1] [6,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11510

lemma sg11885 : RowSquare [8,6,2,2,2,2,1,1] [6,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11511

lemma sg11886 : RowSquare [8,6,2,2,2,2,1,1] [6,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11512

lemma sg11887 : RowSquare [8,6,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11513

lemma sg11888 : RowSquare [8,6,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg11514

lemma sg11889 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7257

lemma sg11890 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6126

lemma sg11891 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8692

lemma sg11892 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8693

lemma sg11893 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8694

lemma sg11894 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8695

lemma sg11895 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg8696

lemma sg11896 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6127

lemma sg11897 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11515

lemma sg11898 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11516

lemma sg11899 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11517

lemma sg11900 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg11518

lemma sg11901 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11519

lemma sg11902 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11520

lemma sg11903 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11521

lemma sg11904 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg11522

lemma sg11905 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11523

lemma sg11906 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg810 sg2547

lemma sg11907 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg818 sg2546

lemma sg11908 : RowSquare [8,6,2,2,2,2,1,1] [6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7256

lemma sg11909 : RowSquare [8,6,2,2,2,2,1,1] [6,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7258

lemma sg11910 : RowSquare [8,6,2,2,2,2,1,1] [6,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6128

lemma sg11911 : RowSquare [8,6,2,2,2,2,1,1] [6,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8684

lemma sg11912 : RowSquare [8,6,2,2,2,2,1,1] [6,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8685

lemma sg11913 : RowSquare [8,6,2,2,2,2,1,1] [6,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8686

lemma sg11914 : RowSquare [8,6,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8687

lemma sg11915 : RowSquare [8,6,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg8688

lemma sg11916 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6126

lemma sg11917 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6129

lemma sg11918 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8697

lemma sg11919 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8698

lemma sg11920 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8699

lemma sg11921 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg8700

lemma sg11922 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6130

lemma sg11923 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11524

lemma sg11924 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11525

lemma sg11925 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11526

lemma sg11926 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg6131

lemma sg11927 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11527

lemma sg11928 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg769 sg2576

lemma sg11929 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1202 sg2039

lemma sg11930 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11528

lemma sg11931 : RowSquare [8,6,2,2,2,2,1,1] [6,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg811 sg2547

lemma sg11932 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7259

lemma sg11933 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5278

lemma sg11934 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7260

lemma sg11935 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7261

lemma sg11936 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7262

lemma sg11937 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg97 sg5281

lemma sg11938 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6132

lemma sg11939 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11529

lemma sg11940 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg763 sg2577

lemma sg11941 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg810 sg2549

lemma sg11942 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg762 sg2583

lemma sg11943 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg763 sg2578

lemma sg11944 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1203 sg2039

lemma sg11945 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg807 sg2550

lemma sg11946 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6133

lemma sg11947 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg764 sg2577

lemma sg11948 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5279

lemma sg11949 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg820 sg2546

lemma sg11950 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg762 sg2584

lemma sg11951 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1204 sg2039

lemma sg11952 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg808 sg2550

lemma sg11953 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1205 sg2039

lemma sg11954 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg809 sg2550

lemma sg11955 : RowSquare [8,6,2,2,2,2,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7258

lemma sg11956 : RowSquare [8,6,2,2,2,2,1,1] [6,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6128

lemma sg11957 : RowSquare [8,6,2,2,2,2,1,1] [6,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7466

lemma sg11958 : RowSquare [8,6,2,2,2,2,1,1] [6,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1681 sg1608

lemma sg11959 : RowSquare [8,6,2,2,2,2,1,1] [6,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1681 sg1607

lemma sg11960 : RowSquare [8,6,2,2,2,2,1,1] [6,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1681 sg1605

lemma sg11961 : RowSquare [8,6,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1681 sg1603

lemma sg11962 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6129

lemma sg11963 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6134

lemma sg11964 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7265

lemma sg11965 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7266

lemma sg11966 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7267

lemma sg11967 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg40 sg6131

lemma sg11968 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7467

lemma sg11969 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7468

lemma sg11970 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg765 sg2577

lemma sg11971 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1202 sg2040

lemma sg11972 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg762 sg2585

lemma sg11973 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2041

lemma sg11974 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1206 sg2039

lemma sg11975 : RowSquare [8,6,2,2,2,2,1,1] [6,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg814 sg2547

lemma sg11976 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5282

lemma sg11977 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6136

lemma sg11978 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8701

lemma sg11979 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg763 sg2579

lemma sg11980 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1202 sg2042

lemma sg11981 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4625

lemma sg11982 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg764 sg2579

lemma sg11983 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4626

lemma sg11984 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1203 sg2040

lemma sg11985 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2043

lemma sg11986 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1203 sg2041

lemma sg11987 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg8702

lemma sg11988 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg767 sg2577

lemma sg11989 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2044

lemma sg11990 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1204 sg2040

lemma sg11991 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1205 sg2040

lemma sg11992 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1204 sg2041

lemma sg11993 : RowSquare [8,6,2,2,2,2,1,1] [6,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1205 sg2041

lemma sg11994 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5283

lemma sg11995 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4627

lemma sg11996 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg773 sg2576

lemma sg11997 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg209 sg4624

lemma sg11998 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1203 sg2042

lemma sg11999 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2577

lemma sg12000 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2578

lemma sg12001 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1204 sg2042

lemma sg12002 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1203 sg2043

lemma sg12003 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg763 sg2581

lemma sg12004 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg3798

lemma sg12005 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1203 sg2044

lemma sg12006 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg808 sg2552

lemma sg12007 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1204 sg2043

lemma sg12008 : RowSquare [8,6,2,2,2,2,1,1] [6,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg456 sg3279

lemma sg12009 : RowSquare [8,6,2,2,2,2,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7263

lemma sg12010 : RowSquare [8,6,2,2,2,2,1,1] [6,6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7264

lemma sg12011 : RowSquare [8,6,2,2,2,2,1,1] [6,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7469

lemma sg12012 : RowSquare [8,6,2,2,2,2,1,1] [6,6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7265

lemma sg12013 : RowSquare [8,6,2,2,2,2,1,1] [6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7266

lemma sg12014 : RowSquare [8,6,2,2,2,2,1,1] [6,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7267

lemma sg12015 : RowSquare [8,6,2,2,2,2,1,1] [6,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg7268

lemma sg12016 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6134

lemma sg12017 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7470

lemma sg12018 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1680 sg1604

lemma sg12019 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg765 sg2579

lemma sg12020 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg40 sg6135

lemma sg12021 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7471

lemma sg12022 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg774 sg2576

lemma sg12023 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7472

lemma sg12024 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1206 sg2040

lemma sg12025 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg762 sg2586

lemma sg12026 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1206 sg2041

lemma sg12027 : RowSquare [8,6,2,2,2,2,1,1] [6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg97 sg5286

lemma sg12028 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6136

lemma sg12029 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4628

lemma sg12030 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg766 sg2579

lemma sg12031 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg210 sg4624

lemma sg12032 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1206 sg2042

lemma sg12033 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg767 sg2579

lemma sg12034 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4629

lemma sg12035 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg807 sg2556

lemma sg12036 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1206 sg2043

lemma sg12037 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,3,3,2] := by
  exact rowSquare_join (by decide) sg765 sg2581

lemma sg12038 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg3799

lemma sg12039 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1206 sg2044

lemma sg12040 : RowSquare [8,6,2,2,2,2,1,1] [6,6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg808 sg2556

lemma sg12041 : RowSquare [8,6,2,2,2,2,1,1] [6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5284

lemma sg12042 : RowSquare [8,6,2,2,2,2,1,1] [6,6,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg768 sg2579

lemma sg12043 : RowSquare [8,6,2,2,2,2,1,1] [6,6,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5285

lemma sg12044 : RowSquare [8,6,2,2,2,2,1,1] [6,6,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg807 sg2558

lemma sg12045 : RowSquare [8,6,2,2,2,2,1,1] [6,6,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg3800

lemma sg12046 : RowSquare [8,6,2,2,2,2,1,1] [6,6,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1207 sg2042

lemma sg12047 : RowSquare [8,6,2,2,2,2,1,1] [6,6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg807 sg2559

lemma sg12048 : RowSquare [8,6,2,2,2,2,1,1] [6,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg459 sg3278

lemma sg12049 : RowSquare [8,6,2,2,2,2,1,1] [6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4630

lemma sg12050 : RowSquare [8,6,2,2,2,2,1,1] [6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1208 sg2042

lemma sg12051 : RowSquare [8,6,2,2,2,2,1,1] [6,6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg807 sg2561

lemma sg12052 : RowSquare [8,6,2,2,2,2,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg8682

lemma sg12053 : RowSquare [8,6,2,2,2,2,1,1] [7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8691

lemma sg12054 : RowSquare [8,6,2,2,2,2,1,1] [7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7269

lemma sg12055 : RowSquare [8,6,2,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7473

lemma sg12056 : RowSquare [8,6,2,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10588

lemma sg12057 : RowSquare [8,6,2,2,2,2,1,1] [7,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10589

lemma sg12058 : RowSquare [8,6,2,2,2,2,1,1] [7,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10590

lemma sg12059 : RowSquare [8,6,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10591

lemma sg12060 : RowSquare [8,6,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg10592

lemma sg12061 : RowSquare [8,6,2,2,2,2,1,1] [7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7269

lemma sg12062 : RowSquare [8,6,2,2,2,2,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7270

lemma sg12063 : RowSquare [8,6,2,2,2,2,1,1] [7,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6137

lemma sg12064 : RowSquare [8,6,2,2,2,2,1,1] [7,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8692

lemma sg12065 : RowSquare [8,6,2,2,2,2,1,1] [7,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8693

lemma sg12066 : RowSquare [8,6,2,2,2,2,1,1] [7,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8694

lemma sg12067 : RowSquare [8,6,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8695

lemma sg12068 : RowSquare [8,6,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg8696

lemma sg12069 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg6126

lemma sg12070 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6138

lemma sg12071 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8703

lemma sg12072 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8704

lemma sg12073 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg8705

lemma sg12074 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg8706

lemma sg12075 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5280

lemma sg12076 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7474

lemma sg12077 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7475

lemma sg12078 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg7476

lemma sg12079 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg98 sg5281

lemma sg12080 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg10593

lemma sg12081 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg776 sg2576

lemma sg12082 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1209 sg2039

lemma sg12083 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg810 sg2550

lemma sg12084 : RowSquare [8,6,2,2,2,2,1,1] [7,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg818 sg2547

lemma sg12085 : RowSquare [8,6,2,2,2,2,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7270

lemma sg12086 : RowSquare [8,6,2,2,2,2,1,1] [7,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6137

lemma sg12087 : RowSquare [8,6,2,2,2,2,1,1] [7,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6139

lemma sg12088 : RowSquare [8,6,2,2,2,2,1,1] [7,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8697

lemma sg12089 : RowSquare [8,6,2,2,2,2,1,1] [7,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8698

lemma sg12090 : RowSquare [8,6,2,2,2,2,1,1] [7,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg8699

lemma sg12091 : RowSquare [8,6,2,2,2,2,1,1] [7,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg8700

lemma sg12092 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6138

lemma sg12093 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5282

lemma sg12094 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7271

lemma sg12095 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7272

lemma sg12096 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7273

lemma sg12097 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg99 sg5281

lemma sg12098 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6140

lemma sg12099 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11530

lemma sg12100 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg769 sg2577

lemma sg12101 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1202 sg2045

lemma sg12102 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg762 sg2587

lemma sg12103 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2046

lemma sg12104 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1210 sg2039

lemma sg12105 : RowSquare [8,6,2,2,2,2,1,1] [7,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg811 sg2550

lemma sg12106 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5287

lemma sg12107 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg98 sg5283

lemma sg12108 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7274

lemma sg12109 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg763 sg2583

lemma sg12110 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1209 sg2042

lemma sg12111 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg4631

lemma sg12112 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg764 sg2583

lemma sg12113 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg810 sg2552

lemma sg12114 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1203 sg2045

lemma sg12115 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg2043

lemma sg12116 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1203 sg2046

lemma sg12117 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg770 sg2577

lemma sg12118 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1209 sg2044

lemma sg12119 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1204 sg2045

lemma sg12120 : RowSquare [8,6,2,2,2,2,1,1] [7,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1205 sg2045

lemma sg12121 : RowSquare [8,6,2,2,2,2,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg6128

lemma sg12122 : RowSquare [8,6,2,2,2,2,1,1] [7,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg6139

lemma sg12123 : RowSquare [8,6,2,2,2,2,1,1] [7,5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6141

lemma sg12124 : RowSquare [8,6,2,2,2,2,1,1] [7,5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7271

lemma sg12125 : RowSquare [8,6,2,2,2,2,1,1] [7,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7272

lemma sg12126 : RowSquare [8,6,2,2,2,2,1,1] [7,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg7273

lemma sg12127 : RowSquare [8,6,2,2,2,2,1,1] [7,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg42 sg6131

lemma sg12128 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5289

lemma sg12129 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg6142

lemma sg12130 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7276

lemma sg12131 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg763 sg2585

lemma sg12132 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1202 sg2047

lemma sg12133 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg4625

lemma sg12134 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg764 sg2585

lemma sg12135 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2048

lemma sg12136 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1206 sg2045

lemma sg12137 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1202 sg2049

lemma sg12138 : RowSquare [8,6,2,2,2,2,1,1] [7,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1206 sg2046

lemma sg12139 : RowSquare [8,6,2,2,2,2,1,1] [7,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg5290

end UniversalTensorSquare
end
end

end OAI
