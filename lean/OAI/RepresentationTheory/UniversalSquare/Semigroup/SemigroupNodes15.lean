import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes13
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes11

namespace OAI

/-! Semigroup Nodes 15. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg6534 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1069 sg1105

lemma sg6535 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1068 sg1106

lemma sg6536 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1070 sg1105

lemma sg6537 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,2] := by
  exact rowSquare_join (by decide) sg1061 sg1117

lemma sg6538 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1068 sg1107

lemma sg6539 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1061 sg1118

lemma sg6540 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1069 sg1107

lemma sg6541 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,4,4] := by
  exact rowSquare_join (by decide) sg1072 sg1105

lemma sg6542 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg1068 sg1108

lemma sg6543 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,5,2,1] := by
  exact rowSquare_join (by decide) sg1069 sg1108

lemma sg6544 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,5,5,3] := by
  exact rowSquare_join (by decide) sg1105 sg1073

lemma sg6545 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1070 sg1106

lemma sg6546 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1068 sg1109

lemma sg6547 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,6,3,2,2] := by
  exact rowSquare_join (by decide) sg1061 sg1119

lemma sg6548 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,6,3,3,1] := by
  exact rowSquare_join (by decide) sg1069 sg1109

lemma sg6549 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1068 sg1110

lemma sg6550 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,6,4,2,1] := by
  exact rowSquare_join (by decide) sg1069 sg1110

lemma sg6551 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,6,4,3] := by
  exact rowSquare_join (by decide) sg1072 sg1107

lemma sg6552 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,7,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1070 sg1109

lemma sg6553 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,7,2,2,2] := by
  exact rowSquare_join (by decide) sg694 sg1545

lemma sg6554 : RowSquare [3,3,2,2,2,1,1,1,1,1,1,1,1] [7,7,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1070 sg1110

lemma sg6555 : RowSquare [4,3,2,2,2,2,2,2,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg982 sg879

lemma sg6556 : RowSquare [4,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg1061

lemma sg6557 : RowSquare [4,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg390 sg1891

lemma sg6558 : RowSquare [4,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1032 sg1061

lemma sg6559 : RowSquare [4,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1061 sg1033

lemma sg6560 : RowSquare [4,3,3,2,1,1,1,1,1,1,1,1] [5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1061 sg1037

lemma sg6561 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg1092

lemma sg6562 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg673 sg1520

lemma sg6563 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg1031

lemma sg6564 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg1032

lemma sg6565 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg1033

lemma sg6566 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1032

lemma sg6567 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1032 sg1033

lemma sg6568 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg1033

lemma sg6569 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg673 sg1417

lemma sg6570 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1034 sg1033

lemma sg6571 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg613 sg1520

lemma sg6572 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1521

lemma sg6573 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg1035

lemma sg6574 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1035 sg1032

lemma sg6575 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1035 sg1033

lemma sg6576 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1522

lemma sg6577 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg1036

lemma sg6578 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1523

lemma sg6579 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg1037

lemma sg6580 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1036

lemma sg6581 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1036 sg1033

lemma sg6582 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg676 sg1417

lemma sg6583 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg1037

lemma sg6584 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1033 sg1037

lemma sg6585 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1961

lemma sg6586 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg1520

lemma sg6587 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1962

lemma sg6588 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg1038

lemma sg6589 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1963

lemma sg6590 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg616 sg1520

lemma sg6591 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1038

lemma sg6592 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1038 sg1033

lemma sg6593 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg1039

lemma sg6594 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1521

lemma sg6595 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg1040

lemma sg6596 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg1039

lemma sg6597 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg1039

lemma sg6598 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1040

lemma sg6599 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1033 sg1040

lemma sg6600 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg1041

lemma sg6601 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg1522

lemma sg6602 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1041

lemma sg6603 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1033 sg1041

lemma sg6604 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg616 sg1523

lemma sg6605 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg373 sg1908

lemma sg6606 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg1095

lemma sg6607 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1043

lemma sg6608 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1093 sg961

lemma sg6609 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1036 sg1036

lemma sg6610 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg1044

lemma sg6611 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1528

lemma sg6612 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1036 sg1038

lemma sg6613 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg1046

lemma sg6614 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1036 sg1039

lemma sg6615 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1968

lemma sg6616 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1038 sg1038

lemma sg6617 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1038 sg1039

lemma sg6618 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1034 sg1045

lemma sg6619 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1096 sg961

lemma sg6620 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg1098

lemma sg6621 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1036 sg1043

lemma sg6622 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg1051

lemma sg6623 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1036 sg1044

lemma sg6624 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg1099

lemma sg6625 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg1100

lemma sg6626 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1969

lemma sg6627 : RowSquare [4,4,2,2,1,1,1,1,1,1,1,1] [8,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg1057

lemma sg6628 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg1891

lemma sg6629 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg178 sg2311

lemma sg6630 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg1892

lemma sg6631 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1893

lemma sg6632 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg331 sg1891

lemma sg6633 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg178 sg2314

lemma sg6634 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg2316

lemma sg6635 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg332 sg1891

lemma sg6636 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg941

lemma sg6637 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1896

lemma sg6638 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg943

lemma sg6639 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg334 sg1891

lemma sg6640 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg942

lemma sg6641 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1032 sg943

lemma sg6642 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg943

lemma sg6643 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1092

lemma sg6644 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1093

lemma sg6645 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg940 sg1034

lemma sg6646 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1094

lemma sg6647 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1034 sg941

lemma sg6648 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1095

lemma sg6649 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1034 sg942

lemma sg6650 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg1795

lemma sg6651 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1034 sg943

lemma sg6652 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg370 sg1796

lemma sg6653 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg179 sg2314

lemma sg6654 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg940 sg1035

lemma sg6655 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1036

lemma sg6656 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg945

lemma sg6657 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1037

lemma sg6658 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1035 sg942

lemma sg6659 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1035 sg943

lemma sg6660 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg371 sg1796

lemma sg6661 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg613 sg1413

lemma sg6662 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg946

lemma sg6663 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg548 sg1523

lemma sg6664 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg947

lemma sg6665 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg946

lemma sg6666 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1036 sg943

lemma sg6667 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1795

lemma sg6668 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg947

lemma sg6669 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1033 sg947

lemma sg6670 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1038

lemma sg6671 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg1411

lemma sg6672 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1039

lemma sg6673 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg948

lemma sg6674 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg940 sg1040

lemma sg6675 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1412

lemma sg6676 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg948

lemma sg6677 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1038 sg943

lemma sg6678 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg949

lemma sg6679 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg550 sg1521

lemma sg6680 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg950

lemma sg6681 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg949

lemma sg6682 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg949

lemma sg6683 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg950

lemma sg6684 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1033 sg950

lemma sg6685 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1900

lemma sg6686 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg951

lemma sg6687 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg1413

lemma sg6688 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg951

lemma sg6689 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1033 sg951

lemma sg6690 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg551 sg1523

lemma sg6691 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg952

lemma sg6692 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1092 sg853

lemma sg6693 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1092 sg854

lemma sg6694 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg374 sg1796

lemma sg6695 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1035 sg945

lemma sg6696 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg953

lemma sg6697 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1035 sg947

lemma sg6698 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg953

lemma sg6699 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1093 sg854

lemma sg6700 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg954

lemma sg6701 : RowSquare [4,4,3,2,1,1,1,1,1,1,1] [6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg955

lemma sg6702 : RowSquare [5,3,2,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1108

lemma sg6703 : RowSquare [5,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1064

lemma sg6704 : RowSquare [5,3,3,2,1,1,1,1,1,1,1] [4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1065

lemma sg6705 : RowSquare [5,3,3,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg978

lemma sg6706 : RowSquare [5,3,3,2,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg979

lemma sg6707 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1092

lemma sg6708 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1093

lemma sg6709 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1092

lemma sg6710 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1094

lemma sg6711 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1092

lemma sg6712 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1095

lemma sg6713 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1092 sg1000

lemma sg6714 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1092 sg1001

lemma sg6715 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1093

lemma sg6716 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1093

lemma sg6717 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1093

lemma sg6718 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1093 sg1001

lemma sg6719 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1096

lemma sg6720 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1002 sg1092

lemma sg6721 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1097

lemma sg6722 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1003 sg1092

lemma sg6723 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1098

lemma sg6724 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [7,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1099

lemma sg6725 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1100

lemma sg6726 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1031

lemma sg6727 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1032

lemma sg6728 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1033

lemma sg6729 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1520

lemma sg6730 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1521

lemma sg6731 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1031

lemma sg6732 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1032

lemma sg6733 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1033

lemma sg6734 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1522

lemma sg6735 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1523

lemma sg6736 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1000

lemma sg6737 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1032 sg1001

lemma sg6738 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg1001

lemma sg6739 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1092

lemma sg6740 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1034

lemma sg6741 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1093

lemma sg6742 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1035

lemma sg6743 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1034

lemma sg6744 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1094

lemma sg6745 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1036

lemma sg6746 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1095

lemma sg6747 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1037

lemma sg6748 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1034 sg1000

lemma sg6749 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1034 sg1001

lemma sg6750 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1038

lemma sg6751 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1035

lemma sg6752 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1039

lemma sg6753 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1040

lemma sg6754 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1037

lemma sg6755 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1041

lemma sg6756 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1522

lemma sg6757 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1523

lemma sg6758 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1527

lemma sg6759 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1038

lemma sg6760 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1528

lemma sg6761 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1039

lemma sg6762 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1040

lemma sg6763 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1529

lemma sg6764 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1041

lemma sg6765 : RowSquare [5,4,2,1,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1100

lemma sg6766 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1032

lemma sg6767 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1034

lemma sg6768 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg1416

lemma sg6769 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg1417

lemma sg6770 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1422

lemma sg6771 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg958 sg998

lemma sg6772 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1423

lemma sg6773 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg958 sg999

lemma sg6774 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1424

lemma sg6775 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg958 sg1000

lemma sg6776 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg1417

lemma sg6777 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg1001

lemma sg6778 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1425

lemma sg6779 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1416

lemma sg6780 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg913

lemma sg6781 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1426

lemma sg6782 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1416

lemma sg6783 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg914

lemma sg6784 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg915

lemma sg6785 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1417

lemma sg6786 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg914

lemma sg6787 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1032 sg915

lemma sg6788 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg915

lemma sg6789 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg962

lemma sg6790 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg958 sg1002

lemma sg6791 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg5890

lemma sg6792 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1045

lemma sg6793 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5891

lemma sg6794 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg5892

lemma sg6795 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5893

lemma sg6796 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1047

lemma sg6797 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5894

lemma sg6798 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg5895

lemma sg6799 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5896

lemma sg6800 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5897

lemma sg6801 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg5898

lemma sg6802 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg5899

lemma sg6803 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5900

lemma sg6804 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg5901

lemma sg6805 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg0 sg5902

lemma sg6806 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1435

lemma sg6807 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg1422

lemma sg6808 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1049

lemma sg6809 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1436

lemma sg6810 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg1008

lemma sg6811 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1424

lemma sg6812 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg920

lemma sg6813 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1038 sg915

lemma sg6814 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1437

lemma sg6815 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1377

lemma sg6816 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg921

lemma sg6817 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg921

lemma sg6818 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg922

lemma sg6819 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1033 sg922

lemma sg6820 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg923

lemma sg6821 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg615 sg1378

lemma sg6822 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg923

lemma sg6823 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg1033 sg923

lemma sg6824 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg616 sg1379

lemma sg6825 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg373 sg1782

lemma sg6826 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1050

lemma sg6827 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg5903

lemma sg6828 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1051

lemma sg6829 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1052

lemma sg6830 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg968

lemma sg6831 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5904

lemma sg6832 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg5905

lemma sg6833 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg969

lemma sg6834 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5906

lemma sg6835 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg5907

lemma sg6836 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5908

lemma sg6837 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1053

lemma sg6838 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg970

lemma sg6839 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1054

lemma sg6840 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg971

lemma sg6841 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5909

lemma sg6842 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5101

lemma sg6843 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg5910

lemma sg6844 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5102

lemma sg6845 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5103

lemma sg6846 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg5104

lemma sg6847 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5105

lemma sg6848 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1 sg5106

lemma sg6849 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1055

lemma sg6850 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg972

lemma sg6851 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5912

lemma sg6852 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg5914

lemma sg6853 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1056

lemma sg6854 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1447

lemma sg6855 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg2596

lemma sg6856 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1057

lemma sg6857 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1058

lemma sg6858 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg973

lemma sg6859 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1059

lemma sg6860 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg974

lemma sg6861 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5107

lemma sg6862 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5108

lemma sg6863 : RowSquare [5,4,2,2,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1060

lemma sg6864 : RowSquare [5,4,2,2,2,2,2,1] [4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg2596

lemma sg6865 : RowSquare [5,4,2,2,2,2,2,1] [4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg2597

lemma sg6866 : RowSquare [5,4,2,2,2,2,2,1] [5,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg2597

lemma sg6867 : RowSquare [5,4,2,2,2,2,2,1] [5,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg85 sg2596

lemma sg6868 : RowSquare [5,4,2,2,2,2,2,1] [5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg838 sg880

lemma sg6869 : RowSquare [5,4,2,2,2,2,2,1] [5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg2603

lemma sg6870 : RowSquare [5,4,2,2,2,2,2,1] [5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg882

lemma sg6871 : RowSquare [5,4,2,2,2,2,2,1] [5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg2604

lemma sg6872 : RowSquare [5,4,2,2,2,2,2,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg884

lemma sg6873 : RowSquare [5,4,2,2,2,2,2,1] [5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg2607

lemma sg6874 : RowSquare [5,4,2,2,2,2,2,1] [5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg885

lemma sg6875 : RowSquare [5,4,2,2,2,2,2,1] [6,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg85 sg2597

lemma sg6876 : RowSquare [5,4,2,2,2,2,2,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg86 sg2596

lemma sg6877 : RowSquare [5,4,2,2,2,2,2,1] [8,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg86 sg2597

lemma sg6878 : RowSquare [5,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg849 sg997

lemma sg6879 : RowSquare [5,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1682

lemma sg6880 : RowSquare [5,4,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg849 sg998

lemma sg6881 : RowSquare [5,4,3,2,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg999

lemma sg6882 : RowSquare [5,4,3,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1682

lemma sg6883 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg374 sg1682

lemma sg6884 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg1683

lemma sg6885 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1002

lemma sg6886 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg850 sg997

lemma sg6887 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg1683

lemma sg6888 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg1003

lemma sg6889 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg850 sg998

lemma sg6890 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg370 sg1688

lemma sg6891 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg377 sg1682

lemma sg6892 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg378 sg1682

lemma sg6893 : RowSquare [5,4,3,2,1,1,1,1,1,1] [4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg371 sg1688

lemma sg6894 : RowSquare [5,4,3,2,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg374 sg1683

lemma sg6895 : RowSquare [5,4,3,2,1,1,1,1,1,1] [5,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg375 sg1683

lemma sg6896 : RowSquare [5,4,3,2,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg376 sg1683

lemma sg6897 : RowSquare [5,4,3,2,1,1,1,1,1,1] [5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg374 sg1688

lemma sg6898 : RowSquare [5,4,3,2,1,1,1,1,1,1] [5,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg377 sg1683

lemma sg6899 : RowSquare [5,4,3,2,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg378 sg1683

lemma sg6900 : RowSquare [5,4,3,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg1682

lemma sg6901 : RowSquare [5,4,3,2,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg3299

lemma sg6902 : RowSquare [5,4,3,2,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg1683

lemma sg6903 : RowSquare [5,4,3,2,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg3300

lemma sg6904 : RowSquare [5,4,3,2,1,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg3301

lemma sg6905 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg997 sg997

lemma sg6906 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg998

lemma sg6907 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg999

lemma sg6908 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1000

lemma sg6909 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1001

lemma sg6910 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg998

lemma sg6911 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg999

lemma sg6912 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1000

lemma sg6913 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1001

lemma sg6914 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg999

lemma sg6915 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1000

lemma sg6916 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1001

lemma sg6917 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg1000

lemma sg6918 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1000 sg1001

lemma sg6919 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg1001

lemma sg6920 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg997 sg1002

lemma sg6921 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1003

lemma sg6922 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1002

lemma sg6923 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1004

lemma sg6924 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1002 sg999

lemma sg6925 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1005

lemma sg6926 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1000

lemma sg6927 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1001

lemma sg6928 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1006

lemma sg6929 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1003

lemma sg6930 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1007

lemma sg6931 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1004

lemma sg6932 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1003

lemma sg6933 : RowSquare [5,5,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1008

end UniversalTensorSquare
end
end

end OAI
