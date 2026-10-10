import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes19

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9738 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1763

lemma sg9739 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg1758

lemma sg9740 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1389

lemma sg9741 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1378

lemma sg9742 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1377

lemma sg9743 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1764

lemma sg9744 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1379

lemma sg9745 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1767

lemma sg9746 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1377

lemma sg9747 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1764

lemma sg9748 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1377

lemma sg9749 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1757

lemma sg9750 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1758

lemma sg9751 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1765

lemma sg9752 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1001 sg1765

lemma sg9753 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1378

lemma sg9754 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1766

lemma sg9755 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1379

lemma sg9756 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1378

lemma sg9757 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1766

lemma sg9758 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1378

lemma sg9759 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1379

lemma sg9760 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1379

lemma sg9761 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1001 sg1767

lemma sg9762 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1390

lemma sg9763 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8230

lemma sg9764 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8231

lemma sg9765 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1018 sg1754

lemma sg9766 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1391

lemma sg9767 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8232

lemma sg9768 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8233

lemma sg9769 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1392

lemma sg9770 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8234

lemma sg9771 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6726

lemma sg9772 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8235

lemma sg9773 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1393

lemma sg9774 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8236

lemma sg9775 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6727

lemma sg9776 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1380 sg1331

lemma sg9777 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6728

lemma sg9778 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1380 sg1332

lemma sg9779 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1009 sg1758

lemma sg9780 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1394

lemma sg9781 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8237

lemma sg9782 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6729

lemma sg9783 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8238

lemma sg9784 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1021 sg1754

lemma sg9785 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1395

lemma sg9786 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8239

lemma sg9787 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6730

lemma sg9788 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6731

lemma sg9789 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8240

lemma sg9790 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8241

lemma sg9791 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6732

lemma sg9792 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1381

lemma sg9793 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6733

lemma sg9794 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1381 sg1332

lemma sg9795 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1396

lemma sg9796 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1387

lemma sg9797 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6734

lemma sg9798 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8242

lemma sg9799 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5831

lemma sg9800 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6735

lemma sg9801 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8245

lemma sg9802 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5832

lemma sg9803 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5833

lemma sg9804 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1382

lemma sg9805 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1012 sg1757

lemma sg9806 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1383

lemma sg9807 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6736

lemma sg9808 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6737

lemma sg9809 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg6738

lemma sg9810 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1022 sg1754

lemma sg9811 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1397

lemma sg9812 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1348

lemma sg9813 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8246

lemma sg9814 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1373 sg1338

lemma sg9815 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1398

lemma sg9816 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1349

lemma sg9817 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8247

lemma sg9818 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8248

lemma sg9819 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5834

lemma sg9820 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8249

lemma sg9821 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1373 sg1340

lemma sg9822 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1384

lemma sg9823 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1338 sg1376

lemma sg9824 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1384

lemma sg9825 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1389

lemma sg9826 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8250

lemma sg9827 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8251

lemma sg9828 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5835

lemma sg9829 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8252

lemma sg9830 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8253

lemma sg9831 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5836

lemma sg9832 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg5837

lemma sg9833 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1386

lemma sg9834 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1386

lemma sg9835 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1376 sg1340

lemma sg9836 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1387

lemma sg9837 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5838

lemma sg9838 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8255

lemma sg9839 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5839

lemma sg9840 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5840

lemma sg9841 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg4 sg5841

lemma sg9842 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5842

lemma sg9843 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg4 sg5843

lemma sg9844 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1023 sg1754

lemma sg9845 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1399

lemma sg9846 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1015 sg1755

lemma sg9847 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1770

lemma sg9848 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1016 sg1755

lemma sg9849 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1388

lemma sg9850 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1771

lemma sg9851 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5844

lemma sg9852 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1885

lemma sg9853 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1015 sg1758

lemma sg9854 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1770

lemma sg9855 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1001 sg1770

lemma sg9856 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1389

lemma sg9857 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1388

lemma sg9858 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5845

lemma sg9859 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5846

lemma sg9860 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5847

lemma sg9861 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1388

lemma sg9862 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1771

lemma sg9863 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg891 sg1885

lemma sg9864 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg892 sg1885

lemma sg9865 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1389

lemma sg9866 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1389

lemma sg9867 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5848

lemma sg9868 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5849

lemma sg9869 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg1340 sg1378

lemma sg9870 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg1340 sg1379

lemma sg9871 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5850

lemma sg9872 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg4 sg5851

lemma sg9873 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [6,6,6,4] := by
  exact rowSquare_join (by decide) sg4 sg5852

lemma sg9874 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1024 sg1754

lemma sg9875 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1400

lemma sg9876 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6739

lemma sg9877 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6740

lemma sg9878 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1025 sg1754

lemma sg9879 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1401

lemma sg9880 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6741

lemma sg9881 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6742

lemma sg9882 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6743

lemma sg9883 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1026 sg1754

lemma sg9884 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1402

lemma sg9885 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6744

lemma sg9886 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6745

lemma sg9887 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5853

lemma sg9888 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6746

lemma sg9889 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6747

lemma sg9890 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6748

lemma sg9891 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1390

lemma sg9892 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6749

lemma sg9893 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1390 sg1332

lemma sg9894 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1027 sg1754

lemma sg9895 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1403

lemma sg9896 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8261

lemma sg9897 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6750

lemma sg9898 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6751

lemma sg9899 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1404

lemma sg9900 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8262

lemma sg9901 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6752

lemma sg9902 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5854

lemma sg9903 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5855

lemma sg9904 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6753

lemma sg9905 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6754

lemma sg9906 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg5832

lemma sg9907 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5833

lemma sg9908 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1391

lemma sg9909 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1396

lemma sg9910 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6755

lemma sg9911 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5856

lemma sg9912 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5857

lemma sg9913 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5858

lemma sg9914 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5054

lemma sg9915 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5859

lemma sg9916 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg5860

lemma sg9917 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5055

lemma sg9918 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5056

lemma sg9919 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg13 sg5057

lemma sg9920 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1028 sg1754

lemma sg9921 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1405

lemma sg9922 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8263

lemma sg9923 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6758

lemma sg9924 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6759

lemma sg9925 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg5834

lemma sg9926 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8264

lemma sg9927 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6760

lemma sg9928 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6761

lemma sg9929 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5861

lemma sg9930 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6762

lemma sg9931 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5058

lemma sg9932 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg5 sg5836

lemma sg9933 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg5 sg5837

lemma sg9934 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6763

lemma sg9935 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6764

lemma sg9936 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5862

lemma sg9937 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5863

lemma sg9938 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5059

lemma sg9939 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5060

lemma sg9940 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg5864

lemma sg9941 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5061

lemma sg9942 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg5062

lemma sg9943 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1396

lemma sg9944 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5063

lemma sg9945 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5865

lemma sg9946 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5064

lemma sg9947 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5065

lemma sg9948 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5066

lemma sg9949 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,5,5,5] := by
  exact rowSquare_join (by decide) sg13 sg5067

lemma sg9950 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1406

lemma sg9951 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1358

lemma sg9952 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8266

lemma sg9953 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1373 sg1348

lemma sg9954 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg5844

lemma sg9955 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8267

lemma sg9956 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8268

lemma sg9957 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5866

lemma sg9958 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5867

lemma sg9959 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5068

lemma sg9960 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5069

lemma sg9961 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg1376 sg1348

lemma sg9962 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8269

lemma sg9963 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5070

lemma sg9964 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5868

lemma sg9965 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5071

lemma sg9966 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5072

lemma sg9967 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5073

lemma sg9968 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5870

lemma sg9969 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5074

lemma sg9970 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5872

lemma sg9971 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5075

lemma sg9972 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,5,4] := by
  exact rowSquare_join (by decide) sg13 sg5076

lemma sg9973 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,6,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5077

lemma sg9974 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,6,6,3] := by
  exact rowSquare_join (by decide) sg13 sg5078

lemma sg9975 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1023 sg1755

lemma sg9976 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1399

lemma sg9977 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1773

lemma sg9978 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1023 sg1758

lemma sg9979 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1006 sg1770

lemma sg9980 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1399

lemma sg9981 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5875

lemma sg9982 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5876

lemma sg9983 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5079

lemma sg9984 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,2] := by
  exact rowSquare_join (by decide) sg1001 sg1773

lemma sg9985 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5877

lemma sg9986 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5080

lemma sg9987 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,4,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5879

lemma sg9988 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5081

lemma sg9989 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,4,4] := by
  exact rowSquare_join (by decide) sg13 sg5082

lemma sg9990 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,5,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5881

lemma sg9991 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,5,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5083

lemma sg9992 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,5,3] := by
  exact rowSquare_join (by decide) sg13 sg5084

lemma sg9993 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,6,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5884

lemma sg9994 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [7,7,6,2] := by
  exact rowSquare_join (by decide) sg4 sg5885

lemma sg9995 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1400

lemma sg9996 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6765

lemma sg9997 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5085

lemma sg9998 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg5 sg5860

lemma sg9999 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5886

lemma sg10000 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5086

lemma sg10001 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg5887

lemma sg10002 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5087

lemma sg10003 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg5088

lemma sg10004 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg9 sg5139

lemma sg10005 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5089

lemma sg10006 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg5057

lemma sg10007 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg9 sg5140

lemma sg10008 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5090

lemma sg10009 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5091

lemma sg10010 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5092

lemma sg10011 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8270

lemma sg10012 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg10 sg5139

lemma sg10013 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5060

lemma sg10014 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5093

lemma sg10015 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5094

lemma sg10016 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5095

lemma sg10017 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,6,4,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5065

lemma sg10018 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5096

lemma sg10019 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,6,4,4] := by
  exact rowSquare_join (by decide) sg13 sg5097

lemma sg10020 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,7,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5069

lemma sg10021 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5098

lemma sg10022 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,2] := by
  exact rowSquare_join (by decide) sg892 sg1890

lemma sg10023 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5099

lemma sg10024 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg3745

lemma sg10025 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg9 sg5147

lemma sg10026 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg3746

lemma sg10027 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg5887

lemma sg10028 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg3747

lemma sg10029 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5100

lemma sg10030 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,2] := by
  exact rowSquare_join (by decide) sg39 sg4554

lemma sg10031 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,1] := by
  exact rowSquare_join (by decide) sg39 sg4555

lemma sg10032 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5085

lemma sg10033 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg27 sg4580

lemma sg10034 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg3748

lemma sg10035 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,2] := by
  exact rowSquare_join (by decide) sg39 sg4556

lemma sg10036 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg3749

lemma sg10037 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,5,4,2,2] := by
  exact rowSquare_join (by decide) sg40 sg4554

lemma sg10038 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,1] := by
  exact rowSquare_join (by decide) sg39 sg4557

lemma sg10039 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,5,4,4] := by
  exact rowSquare_join (by decide) sg39 sg4558

lemma sg10040 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5089

lemma sg10041 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg27 sg4581

lemma sg10042 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,6,3,2,2] := by
  exact rowSquare_join (by decide) sg40 sg4556

lemma sg10043 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg4582

lemma sg10044 : RowSquare [6,5,2,2,2,2,2,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5672

lemma sg10045 : RowSquare [6,5,2,2,2,2,2,1] [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5680

lemma sg10046 : RowSquare [6,5,2,2,2,2,2,1] [5,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5681

lemma sg10047 : RowSquare [6,5,2,2,2,2,2,1] [5,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5682

lemma sg10048 : RowSquare [6,5,2,2,2,2,2,1] [5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5683

lemma sg10049 : RowSquare [6,5,2,2,2,2,2,1] [5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5684

lemma sg10050 : RowSquare [6,5,2,2,2,2,2,1] [5,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5685

lemma sg10051 : RowSquare [6,5,2,2,2,2,2,1] [5,5,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5686

lemma sg10052 : RowSquare [6,5,2,2,2,2,2,1] [5,5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5687

lemma sg10053 : RowSquare [6,5,2,2,2,2,2,1] [5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5688

lemma sg10054 : RowSquare [6,5,2,2,2,2,2,1] [5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5689

lemma sg10055 : RowSquare [6,5,2,2,2,2,2,1] [5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5690

lemma sg10056 : RowSquare [6,5,2,2,2,2,2,1] [5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5691

lemma sg10057 : RowSquare [6,5,2,2,2,2,2,1] [5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5692

lemma sg10058 : RowSquare [6,5,2,2,2,2,2,1] [5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg5693

lemma sg10059 : RowSquare [6,5,2,2,2,2,2,1] [5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5694

lemma sg10060 : RowSquare [6,5,2,2,2,2,2,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5673

lemma sg10061 : RowSquare [6,5,2,2,2,2,2,1] [6,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5675

lemma sg10062 : RowSquare [6,5,2,2,2,2,2,1] [6,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5676

lemma sg10063 : RowSquare [6,5,2,2,2,2,2,1] [6,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5677

lemma sg10064 : RowSquare [6,5,2,2,2,2,2,1] [6,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5678

lemma sg10065 : RowSquare [6,5,2,2,2,2,2,1] [6,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg5679

lemma sg10066 : RowSquare [6,5,2,2,2,2,2,1] [6,5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5697

lemma sg10067 : RowSquare [6,5,2,2,2,2,2,1] [6,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5706

lemma sg10068 : RowSquare [6,5,2,2,2,2,2,1] [6,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5699

lemma sg10069 : RowSquare [6,5,2,2,2,2,2,1] [6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg838 sg1649

lemma sg10070 : RowSquare [6,5,2,2,2,2,2,1] [6,6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5702

lemma sg10071 : RowSquare [6,5,2,2,2,2,2,1] [6,6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5703

lemma sg10072 : RowSquare [6,5,2,2,2,2,2,1] [6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5704

lemma sg10073 : RowSquare [6,5,2,2,2,2,2,1] [6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5705

lemma sg10074 : RowSquare [6,5,2,2,2,2,2,1] [7,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5681

lemma sg10075 : RowSquare [6,5,2,2,2,2,2,1] [7,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5682

lemma sg10076 : RowSquare [6,5,2,2,2,2,2,1] [7,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg5683

lemma sg10077 : RowSquare [6,5,2,2,2,2,2,1] [7,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg15 sg5684

lemma sg10078 : RowSquare [6,5,2,2,2,2,2,1] [7,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5706

lemma sg10079 : RowSquare [6,5,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg2626

lemma sg10080 : RowSquare [6,5,3,2,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg314 sg2626

lemma sg10081 : RowSquare [6,5,3,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg2626

lemma sg10082 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg314 sg2627

lemma sg10083 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg2627

lemma sg10084 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8352

lemma sg10085 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg312 sg2632

lemma sg10086 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg312 sg2633

lemma sg10087 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg319 sg2626

lemma sg10088 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg320 sg2626

lemma sg10089 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg826 sg1757

lemma sg10090 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1688

lemma sg10091 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg313 sg2633

lemma sg10092 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1673

lemma sg10093 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1674

lemma sg10094 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg890 sg1688

lemma sg10095 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1675

lemma sg10096 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg2136

lemma sg10097 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg828 sg1757

lemma sg10098 : RowSquare [6,5,3,2,1,1,1,1,1,1] [4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg891 sg1688

lemma sg10099 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8365

lemma sg10100 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg312 sg2636

lemma sg10101 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg320 sg2627

lemma sg10102 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg8372

lemma sg10103 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1228

lemma sg10104 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg8376

lemma sg10105 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg2626

lemma sg10106 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1646

lemma sg10107 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5119

lemma sg10108 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg897 sg1688

lemma sg10109 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1230

lemma sg10110 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1227

lemma sg10111 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5962

lemma sg10112 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5964

lemma sg10113 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5120

lemma sg10114 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5121

lemma sg10115 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg1647

lemma sg10116 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1676

lemma sg10117 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg831 sg1756

lemma sg10118 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5965

lemma sg10119 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5966

lemma sg10120 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5122

lemma sg10121 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5123

lemma sg10122 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5124

lemma sg10123 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg3766

lemma sg10124 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5125

lemma sg10125 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg74 sg3767

lemma sg10126 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg5126

lemma sg10127 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg74 sg3768

lemma sg10128 : RowSquare [6,5,3,2,1,1,1,1,1,1] [5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg13 sg5127

lemma sg10129 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6890

lemma sg10130 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg6893

lemma sg10131 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1231

lemma sg10132 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg2627

lemma sg10133 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8397

lemma sg10134 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg4622

lemma sg10135 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg3774

lemma sg10136 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg75 sg3768

lemma sg10137 : RowSquare [6,5,3,2,1,1,1,1,1,1] [6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5119

end UniversalTensorSquare
end
end

end OAI
