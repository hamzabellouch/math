import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes2

namespace OAI

/-! Semigroup Nodes 3. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1663 : RowSquare [5,2,1,1,1,1,1] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg586

lemma sg1664 : RowSquare [5,2,1,1,1,1,1] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg586

lemma sg1665 : RowSquare [5,2,1,1,1,1,1] [3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg587

lemma sg1666 : RowSquare [5,2,1,1,1,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg588

lemma sg1667 : RowSquare [5,2,1,1,1,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg589

lemma sg1668 : RowSquare [5,2,1,1,1,1,1] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg586

lemma sg1669 : RowSquare [5,2,1,1,1,1,1] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg587

lemma sg1670 : RowSquare [5,2,1,1,1,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg313

lemma sg1671 : RowSquare [5,2,1,1,1,1,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg17 sg319

lemma sg1672 : RowSquare [5,2,1,1,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg324

lemma sg1673 : RowSquare [5,2,2,1,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg536

lemma sg1674 : RowSquare [5,2,2,1,1,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg314

lemma sg1675 : RowSquare [5,2,2,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

lemma sg1676 : RowSquare [5,2,2,1,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg543

lemma sg1677 : RowSquare [5,2,2,2,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg271

lemma sg1678 : RowSquare [5,3,1,1,1,1] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg586

lemma sg1679 : RowSquare [5,3,1,1,1,1] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1202

lemma sg1680 : RowSquare [5,3,1,1,1,1] [4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg313

lemma sg1681 : RowSquare [5,3,1,1,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg313

lemma sg1683 : RowSquare [5,3,2,1,1] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg82 sg54

lemma sg1684 : RowSquare [5,3,2,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg81 sg54

lemma sg1685 : RowSquare [5,3,2,1,1] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg54

lemma sg1686 : RowSquare [5,3,2,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg53

lemma sg1687 : RowSquare [5,3,2,1,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg80 sg52

lemma sg1688 : RowSquare [5,3,2,1,1] [2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg252

lemma sg1689 : RowSquare [5,3,2,1,1] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg79 sg54

lemma sg1690 : RowSquare [5,3,2,1,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg34 sg118

lemma sg1691 : RowSquare [5,3,2,1,1] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg77 sg54

lemma sg1692 : RowSquare [5,3,2,1,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg77 sg52

lemma sg1693 : RowSquare [5,3,2,1,1] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg34 sg115

lemma sg1694 : RowSquare [5,3,2,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg475

lemma sg1695 : RowSquare [5,3,2,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg116

lemma sg1696 : RowSquare [5,3,2,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg479

lemma sg1697 : RowSquare [5,3,2,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg252

lemma sg1698 : RowSquare [5,3,3,1] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1232

lemma sg1699 : RowSquare [5,3,3,1] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1233

lemma sg1700 : RowSquare [5,3,3,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg1234

lemma sg1701 : RowSquare [5,3,3,1] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg798

lemma sg1702 : RowSquare [5,4,2,1] [3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg849

lemma sg1703 : RowSquare [5,4,2,1] [3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg510

lemma sg1704 : RowSquare [5,4,2,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg511

lemma sg1705 : RowSquare [5,4,2,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg285

lemma sg1706 : RowSquare [5,4,2,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg55

lemma sg1707 : RowSquare [5,4,2,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg286

lemma sg1708 : RowSquare [5,4,2,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg287

lemma sg1709 : RowSquare [5,4,2,1] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg850

lemma sg1710 : RowSquare [5,4,2,1] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg510

lemma sg1711 : RowSquare [5,4,2,1] [4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg512

lemma sg1712 : RowSquare [5,4,2,1] [4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg56

lemma sg1713 : RowSquare [5,4,2,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg854

lemma sg1714 : RowSquare [5,4,2,1] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg511

lemma sg1715 : RowSquare [5,4,2,1] [4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg57

lemma sg1716 : RowSquare [5,4,2,1] [4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg26 sg143

lemma sg1717 : RowSquare [5,4,2,1] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg75 sg55

lemma sg1718 : RowSquare [5,4,2,1] [4,3,3,2] := by
  exact rowSquare_join (by decide) sg39 sg123

lemma sg1719 : RowSquare [5,4,2,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg285

lemma sg1720 : RowSquare [5,4,2,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg27 sg143

lemma sg1721 : RowSquare [5,4,2,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg291

lemma sg1722 : RowSquare [5,4,2,1] [4,4,3,1] := by
  exact rowSquare_join (by decide) sg76 sg55

lemma sg1723 : RowSquare [5,4,2,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg77 sg55

lemma sg1724 : RowSquare [5,4,2,1] [5,3,3,1] := by
  exact rowSquare_join (by decide) sg78 sg55

lemma sg1725 : RowSquare [5,4,2,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg294

lemma sg1726 : RowSquare [5,4,2,1] [5,5,2] := by
  exact rowSquare_join (by decide) sg55 sg80

lemma sg1727 : RowSquare [5,4,2,1] [6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg512

lemma sg1728 : RowSquare [5,4,2,1] [6,6] := by
  exact rowSquare_join (by decide) sg14 sg294

lemma sg1729 : RowSquare [5,4,2,1] [7,5] := by
  exact rowSquare_join (by decide) sg80 sg59

lemma sg1730 : RowSquare [5,4,2,1] [8,4] := by
  exact rowSquare_join (by decide) sg80 sg60

lemma sg1731 : RowSquare [5,4,2,1] [9,3] := by
  exact rowSquare_join (by decide) sg80 sg61

lemma sg1732 : RowSquare [5,4,2,1] [10,2] := by
  exact rowSquare_join (by decide) sg81 sg61

lemma sg1733 : RowSquare [5,4,2,1] [11,1] := by
  exact rowSquare_join (by decide) sg82 sg61

lemma sg1735 : RowSquare [5,4,3] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg516

lemma sg1736 : RowSquare [5,4,3] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg516

lemma sg1737 : RowSquare [5,4,3] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg516

lemma sg1738 : RowSquare [5,4,3] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg11 sg306

lemma sg1739 : RowSquare [5,4,3] [4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg307

lemma sg1740 : RowSquare [5,4,3] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg307

lemma sg1741 : RowSquare [5,4,3] [5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg306

lemma sg1742 : RowSquare [5,4,3] [5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg11 sg307

lemma sg1743 : RowSquare [5,4,3] [6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg307

lemma sg1744 : RowSquare [5,5,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg295

lemma sg1745 : RowSquare [5,5,1,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg300

lemma sg1746 : RowSquare [5,5,1,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg302

lemma sg1747 : RowSquare [5,5,2] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg306

lemma sg1748 : RowSquare [6,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1327

lemma sg1749 : RowSquare [6,1,1,1,1,1,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1331

lemma sg1750 : RowSquare [6,1,1,1,1,1,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg1332

lemma sg1751 : RowSquare [6,1,1,1,1,1,1] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1338

lemma sg1752 : RowSquare [6,1,1,1,1,1,1] [5,4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg1349

lemma sg1753 : RowSquare [6,1,1,1,1,1,1] [6,5,1] := by
  exact rowSquare_join (by decide) sg0 sg1358

lemma sg1755 : RowSquare [6,2,1,1,1,1] [2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg50

lemma sg1756 : RowSquare [6,2,1,1,1,1] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg112

lemma sg1757 : RowSquare [6,2,1,1,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg111

lemma sg1758 : RowSquare [6,2,1,1,1,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg265

lemma sg1759 : RowSquare [6,2,1,1,1,1] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg112

lemma sg1760 : RowSquare [6,2,1,1,1,1] [3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg111

lemma sg1761 : RowSquare [6,2,1,1,1,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg265

lemma sg1762 : RowSquare [6,2,1,1,1,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg530

lemma sg1763 : RowSquare [6,2,1,1,1,1] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg110

lemma sg1764 : RowSquare [6,2,1,1,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg264

lemma sg1765 : RowSquare [6,2,1,1,1,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg262

lemma sg1766 : RowSquare [6,2,1,1,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg262

lemma sg1767 : RowSquare [6,2,1,1,1,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg525

lemma sg1768 : RowSquare [6,2,1,1,1,1] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg519

lemma sg1769 : RowSquare [6,2,1,1,1,1] [4,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg520

lemma sg1770 : RowSquare [6,2,1,1,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg456

lemma sg1771 : RowSquare [6,2,1,1,1,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg520

lemma sg1772 : RowSquare [6,2,1,1,1,1] [4,4,3,1] := by
  exact rowSquare_join (by decide) sg4 sg520

lemma sg1773 : RowSquare [6,2,1,1,1,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg2 sg809

lemma sg1774 : RowSquare [6,2,2,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg313

lemma sg1775 : RowSquare [6,2,2,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg459

lemma sg1776 : RowSquare [6,3,1,1,1] [3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg534

lemma sg1777 : RowSquare [6,3,1,1,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg312

lemma sg1778 : RowSquare [6,3,1,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg535

lemma sg1779 : RowSquare [6,3,1,1,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg313

lemma sg1780 : RowSquare [6,3,1,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg536

lemma sg1781 : RowSquare [6,3,1,1,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg314

lemma sg1782 : RowSquare [6,3,1,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg315

lemma sg1783 : RowSquare [6,3,1,1,1] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg312

lemma sg1784 : RowSquare [6,3,1,1,1] [4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg317

lemma sg1785 : RowSquare [6,3,1,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg313

lemma sg1786 : RowSquare [6,3,1,1,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg270

lemma sg1787 : RowSquare [6,3,1,1,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg319

lemma sg1788 : RowSquare [6,3,1,1,1] [4,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg320

lemma sg1789 : RowSquare [6,3,1,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg543

lemma sg1790 : RowSquare [6,3,1,1,1] [5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg273

lemma sg1791 : RowSquare [6,3,1,1,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg324

lemma sg1792 : RowSquare [6,3,1,1,1] [5,5,2] := by
  exact rowSquare_join (by decide) sg17 sg276

lemma sg1793 : RowSquare [6,3,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg281

lemma sg1794 : RowSquare [6,3,2,1] [3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg330

lemma sg1795 : RowSquare [6,3,2,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg178

lemma sg1796 : RowSquare [6,3,2,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg66

lemma sg1797 : RowSquare [6,3,2,1] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg330

lemma sg1798 : RowSquare [6,3,2,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg178

lemma sg1799 : RowSquare [6,3,2,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg67

lemma sg1800 : RowSquare [6,3,2,1] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg143

lemma sg1801 : RowSquare [6,3,2,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg68

lemma sg1802 : RowSquare [6,3,2,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg144

lemma sg1803 : RowSquare [6,3,2,1] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg850

lemma sg1804 : RowSquare [6,3,2,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg71

lemma sg1805 : RowSquare [6,3,2,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg148

lemma sg1806 : RowSquare [6,3,2,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg76 sg67

lemma sg1807 : RowSquare [6,3,2,1] [4,4,3,1] := by
  exact rowSquare_join (by decide) sg88 sg55

lemma sg1808 : RowSquare [6,3,2,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg89 sg55

lemma sg1809 : RowSquare [6,3,3] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg154

lemma sg1810 : RowSquare [6,3,3] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg516

lemma sg1811 : RowSquare [6,4,1,1] [2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg330

lemma sg1812 : RowSquare [6,4,1,1] [3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg561

lemma sg1813 : RowSquare [6,4,1,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg331

lemma sg1814 : RowSquare [6,4,1,1] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg330

lemma sg1815 : RowSquare [6,4,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg562

lemma sg1816 : RowSquare [6,4,1,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg332

lemma sg1817 : RowSquare [6,4,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg563

lemma sg1818 : RowSquare [6,4,1,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg333

lemma sg1819 : RowSquare [6,4,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg334

lemma sg1820 : RowSquare [6,4,1,1] [4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg565

lemma sg1821 : RowSquare [6,4,1,1] [4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg142

lemma sg1822 : RowSquare [6,4,1,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg879

lemma sg1823 : RowSquare [6,4,1,1] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg331

lemma sg1824 : RowSquare [6,4,1,1] [4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg143

lemma sg1825 : RowSquare [6,4,1,1] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg66 sg83

lemma sg1826 : RowSquare [6,4,1,1] [4,3,3,2] := by
  exact rowSquare_join (by decide) sg39 sg144

lemma sg1827 : RowSquare [6,4,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg295

lemma sg1828 : RowSquare [6,4,1,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg143

lemma sg1829 : RowSquare [6,4,1,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg338

lemma sg1830 : RowSquare [6,4,1,1] [4,4,3,1] := by
  exact rowSquare_join (by decide) sg67 sg83

lemma sg1831 : RowSquare [6,4,1,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg97 sg55

lemma sg1832 : RowSquare [6,4,1,1] [5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg330

lemma sg1833 : RowSquare [6,4,1,1] [5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg565

lemma sg1834 : RowSquare [6,4,1,1] [5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg66 sg84

lemma sg1835 : RowSquare [6,4,1,1] [5,3,3,1] := by
  exact rowSquare_join (by decide) sg98 sg55

lemma sg1836 : RowSquare [6,4,1,1] [5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg143

lemma sg1837 : RowSquare [6,4,1,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg342

lemma sg1838 : RowSquare [6,4,1,1] [5,5,2] := by
  exact rowSquare_join (by decide) sg83 sg71

lemma sg1839 : RowSquare [6,4,1,1] [6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg331

lemma sg1840 : RowSquare [6,4,1,1] [6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg142

lemma sg1841 : RowSquare [6,4,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg302

lemma sg1842 : RowSquare [6,4,1,1] [7,5] := by
  exact rowSquare_join (by decide) sg71 sg85

lemma sg1843 : RowSquare [6,4,1,1] [9,3] := by
  exact rowSquare_join (by decide) sg71 sg86

lemma sg1844 : RowSquare [6,4,2] [2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg74

lemma sg1845 : RowSquare [6,4,2] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg75

lemma sg1846 : RowSquare [6,4,2] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg577

lemma sg1847 : RowSquare [6,4,2] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg166

lemma sg1848 : RowSquare [6,4,2] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg350

lemma sg1849 : RowSquare [6,5,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg356

lemma sg1850 : RowSquare [6,5,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg83

lemma sg1851 : RowSquare [6,5,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg357

lemma sg1852 : RowSquare [6,5,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg982

lemma sg1853 : RowSquare [6,5,1] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg75 sg83

lemma sg1854 : RowSquare [6,5,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg356

lemma sg1855 : RowSquare [6,5,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg166

lemma sg1856 : RowSquare [6,5,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg360

lemma sg1857 : RowSquare [6,5,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg83 sg77

lemma sg1858 : RowSquare [6,5,1] [5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg165

lemma sg1859 : RowSquare [6,5,1] [5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg75 sg84

lemma sg1860 : RowSquare [6,5,1] [5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg85

lemma sg1861 : RowSquare [6,5,1] [5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg168

lemma sg1862 : RowSquare [6,5,1] [5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg166

lemma sg1863 : RowSquare [6,5,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg363

lemma sg1864 : RowSquare [6,5,1] [6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg165

lemma sg1865 : RowSquare [6,5,1] [6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg41 sg168

lemma sg1866 : RowSquare [6,5,1] [6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg75 sg85

lemma sg1867 : RowSquare [6,5,1] [6,6] := by
  exact rowSquare_join (by decide) sg14 sg363

lemma sg1868 : RowSquare [6,6] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg364

lemma sg1869 : RowSquare [6,6] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg365

lemma sg1870 : RowSquare [6,6] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg367

lemma sg1872 : RowSquare [7,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1327

lemma sg1873 : RowSquare [7,1,1,1,1,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg1332

lemma sg1874 : RowSquare [7,2,1,1,1] [2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg586

lemma sg1875 : RowSquare [7,2,1,1,1] [3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg586

lemma sg1876 : RowSquare [7,2,1,1,1] [3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg587

lemma sg1877 : RowSquare [7,2,1,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg588

lemma sg1878 : RowSquare [7,2,1,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg589

lemma sg1879 : RowSquare [7,2,1,1,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg590

lemma sg1880 : RowSquare [7,2,1,1,1] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg586

lemma sg1881 : RowSquare [7,2,1,1,1] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg312

lemma sg1882 : RowSquare [7,2,1,1,1] [4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg590

lemma sg1883 : RowSquare [7,2,1,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg313

lemma sg1884 : RowSquare [7,2,1,1,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg314

lemma sg1885 : RowSquare [7,2,1,1,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg17 sg315

lemma sg1886 : RowSquare [7,2,1,1,1] [4,4,3,1] := by
  exact rowSquare_join (by decide) sg4 sg596

lemma sg1887 : RowSquare [7,2,1,1,1] [5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg317

lemma sg1888 : RowSquare [7,2,1,1,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg17 sg319

lemma sg1889 : RowSquare [7,2,1,1,1] [5,5,2] := by
  exact rowSquare_join (by decide) sg17 sg320

lemma sg1890 : RowSquare [7,2,1,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg324

lemma sg1891 : RowSquare [7,2,2,1] [2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg178

lemma sg1892 : RowSquare [7,2,2,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg178

lemma sg1893 : RowSquare [7,2,2,1] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg179

lemma sg1894 : RowSquare [7,2,2,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg178

lemma sg1895 : RowSquare [7,2,2,1] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg180

lemma sg1896 : RowSquare [7,2,2,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg181

lemma sg1897 : RowSquare [7,2,2,1] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg940

lemma sg1898 : RowSquare [7,2,2,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg371

lemma sg1899 : RowSquare [7,2,2,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg88 sg67

lemma sg1900 : RowSquare [7,2,2,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg89 sg68

lemma sg1901 : RowSquare [7,3,1,1] [3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg330

lemma sg1902 : RowSquare [7,3,1,1] [3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg178

lemma sg1903 : RowSquare [7,3,1,1] [3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg330

lemma sg1904 : RowSquare [7,3,1,1] [3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg178

lemma sg1905 : RowSquare [7,3,1,1] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg371

lemma sg1906 : RowSquare [7,3,1,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg615

lemma sg1907 : RowSquare [7,3,1,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg372

lemma sg1908 : RowSquare [7,3,1,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg373

lemma sg1909 : RowSquare [7,3,1,1] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg330

lemma sg1910 : RowSquare [7,3,1,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg961

lemma sg1911 : RowSquare [7,3,1,1] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg178

lemma sg1912 : RowSquare [7,3,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg332

lemma sg1913 : RowSquare [7,3,1,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg377

lemma sg1914 : RowSquare [7,3,2] [3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg87

lemma sg1915 : RowSquare [7,3,2] [3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg88

lemma sg1916 : RowSquare [7,3,2] [3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg194

lemma sg1917 : RowSquare [7,3,2] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg89

lemma sg1918 : RowSquare [7,3,2] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg195

lemma sg1919 : RowSquare [7,3,2] [4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg975

lemma sg1920 : RowSquare [7,3,2] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg92

lemma sg1921 : RowSquare [7,3,2] [5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg306

lemma sg1922 : RowSquare [7,3,2] [5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg577

lemma sg1923 : RowSquare [7,3,2] [6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg307

lemma sg1924 : RowSquare [7,4,1] [3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg97

lemma sg1925 : RowSquare [7,4,1] [3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg207

lemma sg1926 : RowSquare [7,4,1] [3,3,3,3] := by
  exact rowSquare_join (by decide) sg13 sg390

lemma sg1927 : RowSquare [7,4,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg982

lemma sg1929 : RowSquare [7,5] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg402

lemma sg1935 : RowSquare [7,5] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg407

lemma sg1943 : RowSquare [7,5] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg367

lemma sg1944 : RowSquare [8,1,1,1,1] [4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg586

lemma sg1945 : RowSquare [8,1,1,1,1] [4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg998

lemma sg1946 : RowSquare [8,1,1,1,1] [4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg999

lemma sg1947 : RowSquare [8,1,1,1,1] [4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1000

lemma sg1948 : RowSquare [8,1,1,1,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg1001

lemma sg1949 : RowSquare [8,1,1,1,1] [5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg587

lemma sg1950 : RowSquare [8,1,1,1,1] [5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg588

lemma sg1951 : RowSquare [8,1,1,1,1] [5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1006

lemma sg1952 : RowSquare [8,1,1,1,1] [5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1007

lemma sg1953 : RowSquare [8,1,1,1,1] [5,3,2,2] := by
  exact rowSquare_join (by decide) sg2 sg1008

lemma sg1954 : RowSquare [8,2,1,1] [4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg178

lemma sg1955 : RowSquare [8,2,1,1] [4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1032

lemma sg1956 : RowSquare [8,2,1,1] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg1033

lemma sg1957 : RowSquare [8,2,1,1] [4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg178

lemma sg1958 : RowSquare [8,2,1,1] [4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg371

lemma sg1959 : RowSquare [8,2,1,1] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg16 sg372

lemma sg1960 : RowSquare [8,2,1,1] [4,3,3,2] := by
  exact rowSquare_join (by decide) sg16 sg373

lemma sg1961 : RowSquare [8,2,1,1] [4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg371

lemma sg1962 : RowSquare [8,2,1,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg372

lemma sg1963 : RowSquare [8,2,1,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg17 sg373

lemma sg1964 : RowSquare [8,2,1,1] [5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg330

lemma sg1965 : RowSquare [8,2,1,1] [5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg178

lemma sg1966 : RowSquare [8,2,1,1] [5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg179

lemma sg1967 : RowSquare [8,2,1,1] [5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg179

lemma sg1968 : RowSquare [8,2,1,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg17 sg377

lemma sg1969 : RowSquare [8,2,1,1] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg383

lemma sg1970 : RowSquare [8,2,2] [4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg87

lemma sg1971 : RowSquare [8,2,2] [4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg88

lemma sg1972 : RowSquare [8,2,2] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg87 sg89

lemma sg1973 : RowSquare [8,2,2] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg88 sg88

lemma sg1974 : RowSquare [8,2,2] [4,4,3,1] := by
  exact rowSquare_join (by decide) sg88 sg89

lemma sg1975 : RowSquare [8,2,2] [4,4,4] := by
  exact rowSquare_join (by decide) sg89 sg89

lemma sg1976 : RowSquare [8,2,2] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg88 sg92

lemma sg1977 : RowSquare [8,3,1] [4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg87 sg97

lemma sg1978 : RowSquare [8,3,1] [4,3,3,2] := by
  exact rowSquare_join (by decide) sg16 sg390

lemma sg1979 : RowSquare [8,3,1] [4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg228

lemma sg1980 : RowSquare [8,3,1] [4,4,2,2] := by
  exact rowSquare_join (by decide) sg17 sg390

lemma sg1981 : RowSquare [8,3,1] [4,4,3,1] := by
  exact rowSquare_join (by decide) sg88 sg97

lemma sg1982 : RowSquare [8,3,1] [4,4,4] := by
  exact rowSquare_join (by decide) sg97 sg89

lemma sg1983 : RowSquare [8,3,1] [5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg104

lemma sg1984 : RowSquare [8,3,1] [5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg98

lemma sg1985 : RowSquare [8,3,1] [5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg105

lemma sg1986 : RowSquare [8,3,1] [5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg99

lemma sg1987 : RowSquare [8,3,1] [5,3,2,2] := by
  exact rowSquare_join (by decide) sg88 sg98

lemma sg1988 : RowSquare [8,3,1] [5,3,3,1] := by
  exact rowSquare_join (by decide) sg98 sg89

lemma sg1989 : RowSquare [8,3,1] [5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg230

lemma sg1990 : RowSquare [8,3,1] [5,4,2,1] := by
  exact rowSquare_join (by decide) sg88 sg99

lemma sg1991 : RowSquare [8,3,1] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg17 sg394

lemma sg1992 : RowSquare [8,3,1] [6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg106

lemma sg1993 : RowSquare [8,4] [5,3,3,1] := by
  exact rowSquare_join (by decide) sg98 sg97

lemma sg1994 : RowSquare [8,4] [5,4,2,1] := by
  exact rowSquare_join (by decide) sg39 sg228

lemma sg1995 : RowSquare [8,4] [5,4,3] := by
  exact rowSquare_join (by decide) sg97 sg99

lemma sg1996 : RowSquare [8,4] [5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg424

lemma sg1997 : RowSquare [8,4] [6,2,2,2] := by
  exact rowSquare_join (by decide) sg98 sg98

lemma sg1998 : RowSquare [9,1,1,1] [6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg178

lemma sg1999 : RowSquare [9,1,1,1] [6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg371

lemma sg2000 : RowSquare [9,1,1,1] [6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20 sg372

lemma sg2001 : RowSquare [9,1,1,1] [6,2,2,2] := by
  exact rowSquare_join (by decide) sg20 sg373

lemma sg2002 : RowSquare [9,2,1] [6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg104

lemma sg2003 : RowSquare [9,2,1] [6,2,2,2] := by
  exact rowSquare_join (by decide) sg20 sg390

lemma sg2004 : RowSquare [9,2,1] [6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg105

lemma sg2005 : RowSquare [9,2,1] [6,3,2,1] := by
  exact rowSquare_join (by decide) sg88 sg104

lemma sg2006 : RowSquare [9,2,1] [6,4,1,1] := by
  exact rowSquare_join (by decide) sg88 sg105

lemma sg2007 : RowSquare [9,2,1] [6,4,2] := by
  exact rowSquare_join (by decide) sg89 sg105

lemma sg2008 : RowSquare [9,3] [6,3,3] := by
  exact rowSquare_join (by decide) sg97 sg104

lemma sg2009 : RowSquare [9,3] [6,4,2] := by
  exact rowSquare_join (by decide) sg97 sg105

lemma sg2010 : RowSquare [9,3] [6,5,1] := by
  exact rowSquare_join (by decide) sg46 sg228

lemma sg2011 : RowSquare [9,3] [6,6] := by
  exact rowSquare_join (by decide) sg17 sg424

lemma sg2012 : RowSquare [9,3] [7,2,2,1] := by
  exact rowSquare_join (by decide) sg98 sg104

lemma sg2013 : RowSquare [9,3] [7,3,1,1] := by
  exact rowSquare_join (by decide) sg98 sg105

lemma sg2014 : RowSquare [2,2,2,1,1,1,1,1,1,1] [7,6] := by
  exact rowSquare_join (by decide) sg46 sg424

lemma sg2020 : RowSquare [3,2,1,1,1,1,1,1,1,1] [8,5] := by
  exact rowSquare_join (by decide) sg92 sg232

lemma sg2021 : RowSquare [3,3,1,1,1,1,1,1,1] [5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg218

lemma sg2022 : RowSquare [3,3,1,1,1,1,1,1,1] [5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg219

lemma sg2023 : RowSquare [3,3,1,1,1,1,1,1,1] [5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg87 sg220

lemma sg2024 : RowSquare [3,3,1,1,1,1,1,1,1] [5,4,2,2] := by
  exact rowSquare_join (by decide) sg88 sg219

lemma sg2025 : RowSquare [3,3,1,1,1,1,1,1,1] [6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg1063

lemma sg2026 : RowSquare [3,3,1,1,1,1,1,1,1] [7,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg348

lemma sg2027 : RowSquare [3,3,1,1,1,1,1,1,1] [7,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg224

lemma sg2028 : RowSquare [3,3,1,1,1,1,1,1,1] [7,2,2,2] := by
  exact rowSquare_join (by decide) sg90 sg221

lemma sg2029 : RowSquare [3,3,1,1,1,1,1,1,1] [7,4,1,1] := by
  exact rowSquare_join (by decide) sg88 sg225

lemma sg2030 : RowSquare [3,3,1,1,1,1,1,1,1] [7,4,2] := by
  exact rowSquare_join (by decide) sg89 sg225

lemma sg2031 : RowSquare [3,3,1,1,1,1,1,1,1] [7,6] := by
  exact rowSquare_join (by decide) sg92 sg223

lemma sg2032 : RowSquare [3,3,1,1,1,1,1,1,1] [8,2,2,1] := by
  exact rowSquare_join (by decide) sg90 sg224

lemma sg2033 : RowSquare [3,3,1,1,1,1,1,1,1] [8,5] := by
  exact rowSquare_join (by decide) sg92 sg225

lemma sg2034 : RowSquare [3,3,1,1,1,1,1,1,1] [9,2,1,1] := by
  exact rowSquare_join (by decide) sg88 sg226

lemma sg2035 : RowSquare [3,3,2,1,1,1,1,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg33 sg390

lemma sg2036 : RowSquare [3,3,2,2,2,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg165

lemma sg2037 : RowSquare [4,1,1,1,1,1,1,1,1,1] [9,4] := by
  exact rowSquare_join (by decide) sg49 sg383

lemma sg2038 : RowSquare [4,2,2,1,1,1,1,1] [4,4,4,1] := by
  exact rowSquare_join (by decide) sg97 sg181

lemma sg2039 : RowSquare [4,3,1,1,1,1,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg178

lemma sg2040 : RowSquare [4,3,1,1,1,1,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg178

lemma sg2041 : RowSquare [4,3,1,1,1,1,1,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg371

lemma sg2042 : RowSquare [4,3,1,1,1,1,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg178

lemma sg2043 : RowSquare [4,3,1,1,1,1,1,1] [3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg32 sg372

lemma sg2044 : RowSquare [4,3,1,1,1,1,1,1] [3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg373

lemma sg2045 : RowSquare [4,3,1,1,1,1,1,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg90 sg178

lemma sg2046 : RowSquare [4,3,1,1,1,1,1,1] [4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg87 sg179

lemma sg2047 : RowSquare [4,3,1,1,1,1,1,1] [4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg91 sg178

lemma sg2048 : RowSquare [4,3,1,1,1,1,1,1] [4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg88 sg179

lemma sg2049 : RowSquare [4,3,1,1,1,1,1,1] [4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg87 sg180

lemma sg2050 : RowSquare [4,3,1,1,1,1,1,1] [4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg179

lemma sg2051 : RowSquare [4,3,1,1,1,1,1,1] [4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg87 sg181

lemma sg2052 : RowSquare [4,3,1,1,1,1,1,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg33 sg373

lemma sg2053 : RowSquare [4,3,1,1,1,1,1,1] [4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg178

lemma sg2054 : RowSquare [4,3,1,1,1,1,1,1] [4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg371

lemma sg2055 : RowSquare [4,3,1,1,1,1,1,1] [4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg88 sg180

lemma sg2056 : RowSquare [4,3,1,1,1,1,1,1] [4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg89 sg180

lemma sg2057 : RowSquare [4,3,1,1,1,1,1,1] [4,4,3,2] := by
  exact rowSquare_join (by decide) sg88 sg181

lemma sg2058 : RowSquare [4,3,1,1,1,1,1,1] [4,4,4,1] := by
  exact rowSquare_join (by decide) sg89 sg181

lemma sg2059 : RowSquare [4,3,1,1,1,1,1,1] [5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg940

lemma sg2060 : RowSquare [4,3,1,1,1,1,1,1] [5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg93 sg178

lemma sg2061 : RowSquare [4,3,1,1,1,1,1,1] [5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg90 sg179

lemma sg2062 : RowSquare [4,3,1,1,1,1,1,1] [5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg94 sg178

lemma sg2063 : RowSquare [4,3,1,1,1,1,1,1] [5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg91 sg179

lemma sg2064 : RowSquare [4,3,1,1,1,1,1,1] [5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg179

lemma sg2065 : RowSquare [4,3,1,1,1,1,1,1] [5,4,4] := by
  exact rowSquare_join (by decide) sg0 sg1597

lemma sg2066 : RowSquare [4,3,1,1,1,1,1,1] [7,6] := by
  exact rowSquare_join (by decide) sg0 sg1606

lemma sg2067 : RowSquare [4,3,1,1,1,1,1,1] [8,5] := by
  exact rowSquare_join (by decide) sg5 sg722

lemma sg2068 : RowSquare [4,3,1,1,1,1,1,1] [9,4] := by
  exact rowSquare_join (by decide) sg14 sg429

lemma sg2069 : RowSquare [4,3,1,1,1,1,1,1] [10,3] := by
  exact rowSquare_join (by decide) sg14 sg430

lemma sg2070 : RowSquare [4,3,1,1,1,1,1,1] [11,2] := by
  exact rowSquare_join (by decide) sg42 sg235

lemma sg2071 : RowSquare [4,3,1,1,1,1,1,1] [12,1] := by
  exact rowSquare_join (by decide) sg43 sg235

lemma sg2073 : RowSquare [4,3,2,1,1,1,1] [2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg330

lemma sg2074 : RowSquare [4,3,2,1,1,1,1] [2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg178

lemma sg2075 : RowSquare [4,3,2,1,1,1,1] [3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg179

lemma sg2076 : RowSquare [4,3,2,1,1,1,1] [3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg180

lemma sg2077 : RowSquare [4,3,2,1,1,1,1] [4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg849

lemma sg2078 : RowSquare [4,3,2,1,1,1,1] [4,3,3,3] := by
  exact rowSquare_join (by decide) sg33 sg334

lemma sg2079 : RowSquare [4,3,2,2,1,1] [4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg849

lemma sg2080 : RowSquare [4,3,2,2,1,1] [4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg850

lemma sg2081 : RowSquare [4,3,2,2,1,1] [5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg850

lemma sg2082 : RowSquare [4,4,1,1,1,1,1] [3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg66 sg178

lemma sg2083 : RowSquare [4,4,1,1,1,1,1] [3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg178

lemma sg2084 : RowSquare [4,4,1,1,1,1,1] [3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg178

lemma sg2085 : RowSquare [4,4,1,1,1,1,1] [4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg178

end UniversalTensorSquare
end
end

end OAI
