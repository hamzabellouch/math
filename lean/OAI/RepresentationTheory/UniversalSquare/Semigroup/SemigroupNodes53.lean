import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37

namespace OAI

/-! Semigroup Nodes 53. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21740 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg6475 sg6632

lemma sg21741 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6653

lemma sg21742 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg6162 sg7522

lemma sg21743 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg6475 sg6633

lemma sg21744 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7570

lemma sg21745 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6303 sg7314

lemma sg21746 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7571

lemma sg21747 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6785

lemma sg21748 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg5605 sg8411

lemma sg21749 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6786

lemma sg21750 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6794

lemma sg21751 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,4,4,3,2] := by
  exact rowSquare_join (by decide) sg6154 sg7548

lemma sg21752 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg6154 sg7549

lemma sg21753 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7572

lemma sg21754 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6787

lemma sg21755 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6794

lemma sg21756 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,3,3,2] := by
  exact rowSquare_join (by decide) sg6154 sg7550

lemma sg21757 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6300 sg7321

lemma sg21758 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg6309 sg7303

lemma sg21759 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg6154 sg7551

lemma sg21760 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg6178 sg7492

lemma sg21761 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg6186 sg7486

lemma sg21762 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6788

lemma sg21763 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6301 sg7321

lemma sg21764 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg6310 sg7303

lemma sg21765 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg6310 sg7304

lemma sg21766 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6179 sg7492

lemma sg21767 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,6,4,2,1] := by
  exact rowSquare_join (by decide) sg6187 sg7486

lemma sg21768 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg6162 sg7525

lemma sg21769 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,4,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7574

lemma sg21770 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,4,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7575

lemma sg21771 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7576

lemma sg21772 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,4,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7322

lemma sg21773 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg6418 sg6771

lemma sg21774 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7577

lemma sg21775 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7578

lemma sg21776 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7579

lemma sg21777 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7323

lemma sg21778 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7324

lemma sg21779 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg6418 sg6773

lemma sg21780 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7580

lemma sg21781 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7581

lemma sg21782 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7325

lemma sg21783 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7582

lemma sg21784 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7326

lemma sg21785 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6418 sg6775

lemma sg21786 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6634

lemma sg21787 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg6418 sg6776

lemma sg21788 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7583

lemma sg21789 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7327

lemma sg21790 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg6418 sg6777

lemma sg21791 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7328

lemma sg21792 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6635

lemma sg21793 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg6305 sg7308

lemma sg21794 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg6313 sg7304

lemma sg21795 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg6343 sg7286

lemma sg21796 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg6162 sg7528

lemma sg21797 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg6189 sg7486

lemma sg21798 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6176 sg7495

lemma sg21799 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7584

lemma sg21800 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7585

lemma sg21801 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7331

lemma sg21802 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7586

lemma sg21803 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7332

lemma sg21804 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6418 sg6779

lemma sg21805 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6656

lemma sg21806 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg6418 sg6780

lemma sg21807 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7587

lemma sg21808 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7333

lemma sg21809 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7588

lemma sg21810 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7334

lemma sg21811 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6418 sg6782

lemma sg21812 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7335

lemma sg21813 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6658

lemma sg21814 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg6418 sg6783

lemma sg21815 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg6154 sg7558

lemma sg21816 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7589

lemma sg21817 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7336

lemma sg21818 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6659

lemma sg21819 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg6418 sg6784

lemma sg21820 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6660

lemma sg21821 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg6305 sg7313

lemma sg21822 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg6475 sg6635

lemma sg21823 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg6162 sg7530

lemma sg21824 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg6344 sg7286

lemma sg21825 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7590

lemma sg21826 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7337

lemma sg21827 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6305 sg7314

lemma sg21828 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7591

lemma sg21829 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7338

lemma sg21830 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6639

lemma sg21831 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6418 sg6785

lemma sg21832 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6640

lemma sg21833 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6418 sg6786

lemma sg21834 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg6154 sg7561

lemma sg21835 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7339

lemma sg21836 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6641

lemma sg21837 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,5,3,2,2] := by
  exact rowSquare_join (by decide) sg6418 sg6787

lemma sg21838 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,5,3,3,1] := by
  exact rowSquare_join (by decide) sg6154 sg7562

lemma sg21839 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6300 sg7328

lemma sg21840 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg6154 sg7563

lemma sg21841 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6416 sg6788

lemma sg21842 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6417 sg6788

lemma sg21843 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6642

lemma sg21844 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg6418 sg6788

lemma sg21845 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,6,6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6301 sg7328

lemma sg21846 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6176 sg7496

lemma sg21847 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7497

lemma sg21848 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6435 sg6768

lemma sg21849 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7498

lemma sg21850 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6472 sg6661

lemma sg21851 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6436 sg6768

lemma sg21852 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6422 sg6779

lemma sg21853 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6662

lemma sg21854 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg6423 sg6779

lemma sg21855 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg6475 sg6636

lemma sg21856 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7499

lemma sg21857 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6472 sg6663

lemma sg21858 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6437 sg6768

lemma sg21859 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7500

lemma sg21860 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6409 sg6797

lemma sg21861 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6664

lemma sg21862 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6154 sg7564

lemma sg21863 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6665

lemma sg21864 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6425 sg6779

lemma sg21865 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg6154 sg7565

lemma sg21866 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6410 sg6797

lemma sg21867 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6666

lemma sg21868 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg6426 sg6779

lemma sg21869 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg6475 sg6638

lemma sg21870 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6306 sg7313

lemma sg21871 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7644

lemma sg21872 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7099

lemma sg21873 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7501

lemma sg21874 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7337

lemma sg21875 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6409 sg6799

lemma sg21876 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6667

lemma sg21877 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6154 sg7566

lemma sg21878 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7334

lemma sg21879 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6410 sg6799

lemma sg21880 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7338

lemma sg21881 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6668

lemma sg21882 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6425 sg6782

lemma sg21883 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6801

lemma sg21884 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7339

lemma sg21885 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6669

lemma sg21886 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg6426 sg6782

lemma sg21887 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6802

lemma sg21888 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6421 sg6788

lemma sg21889 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6474 sg6642

lemma sg21890 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6307 sg7314

lemma sg21891 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7502

lemma sg21892 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7337

lemma sg21893 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6308 sg7314

lemma sg21894 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6424 sg6786

lemma sg21895 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6803

lemma sg21896 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6309 sg7314

lemma sg21897 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7338

lemma sg21898 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6803

lemma sg21899 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6310 sg7314

lemma sg21900 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6804

lemma sg21901 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7339

lemma sg21902 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6805

lemma sg21903 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6805

lemma sg21904 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6165 sg7514

lemma sg21905 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6297 sg7340

lemma sg21906 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6428 sg6770

lemma sg21907 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7341

lemma sg21908 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7342

lemma sg21909 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg6429 sg6771

lemma sg21910 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6166 sg7514

lemma sg21911 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6297 sg7344

lemma sg21912 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6407 sg6806

lemma sg21913 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7345

lemma sg21914 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6428 sg6772

lemma sg21915 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7346

lemma sg21916 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6432 sg6771

lemma sg21917 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6671

lemma sg21918 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg6429 sg6773

lemma sg21919 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6433 sg6770

lemma sg21920 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7347

lemma sg21921 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6409 sg6806

lemma sg21922 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7348

lemma sg21923 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6434 sg6771

lemma sg21924 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7349

lemma sg21925 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6807

lemma sg21926 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg6154 sg7575

lemma sg21927 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6410 sg6806

lemma sg21928 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7350

lemma sg21929 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6807

lemma sg21930 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg6429 sg6777

lemma sg21931 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6312 sg7308

lemma sg21932 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg6373 sg7036

lemma sg21933 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg6345 sg7286

lemma sg21934 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6297 sg7351

lemma sg21935 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6407 sg6809

lemma sg21936 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7352

lemma sg21937 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6428 sg6778

lemma sg21938 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7353

lemma sg21939 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6436 sg6771

lemma sg21940 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7354

lemma sg21941 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6673

lemma sg21942 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg6429 sg6779

lemma sg21943 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6409 sg6809

lemma sg21944 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7355

lemma sg21945 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6437 sg6771

lemma sg21946 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6410 sg6809

lemma sg21947 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7356

lemma sg21948 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6675

lemma sg21949 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6154 sg7578

lemma sg21950 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6676

lemma sg21951 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6432 sg6775

lemma sg21952 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7357

lemma sg21953 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6677

lemma sg21954 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg6432 sg6777

lemma sg21955 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6312 sg7313

lemma sg21956 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2499 sg12696

lemma sg21957 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6233 sg7481

lemma sg21958 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5294 sg8787

lemma sg21959 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7658

lemma sg21960 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6408 sg6810

lemma sg21961 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7658

lemma sg21962 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5295 sg8787

lemma sg21963 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7093

lemma sg21964 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6408 sg6811

lemma sg21965 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7347

lemma sg21966 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6433 sg6774

lemma sg21967 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7093

lemma sg21968 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7358

lemma sg21969 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7358

lemma sg21970 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6476 sg6634

lemma sg21971 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6154 sg7580

lemma sg21972 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7094

lemma sg21973 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7094

lemma sg21974 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7359

lemma sg21975 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7359

lemma sg21976 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7349

lemma sg21977 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6811

lemma sg21978 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6812

lemma sg21979 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6427 sg6788

lemma sg21980 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7350

lemma sg21981 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6811

lemma sg21982 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6813

lemma sg21983 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6371 sg7044

lemma sg21984 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,6,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6428 sg6788

lemma sg21985 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6315 sg7305

lemma sg21986 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6298 sg7351

lemma sg21987 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7360

lemma sg21988 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6407 sg6814

lemma sg21989 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7360

lemma sg21990 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6315 sg7306

lemma sg21991 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6299 sg7351

lemma sg21992 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7352

lemma sg21993 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6409 sg6814

lemma sg21994 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7361

lemma sg21995 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7361

lemma sg21996 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg5508 sg8637

lemma sg21997 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7307

lemma sg21998 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6410 sg6814

lemma sg21999 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7362

lemma sg22000 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7362

lemma sg22001 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6678

lemma sg22002 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6436 sg6773

lemma sg22003 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7354

lemma sg22004 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6679

lemma sg22005 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6372 sg7039

lemma sg22006 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7352

lemma sg22007 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6431 sg6781

lemma sg22008 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7363

lemma sg22009 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7363

lemma sg22010 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6680

lemma sg22011 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7364

lemma sg22012 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7364

lemma sg22013 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7356

lemma sg22014 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6681

lemma sg22015 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6815

lemma sg22016 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7357

lemma sg22017 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6682

lemma sg22018 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6815

lemma sg22019 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6314 sg7314

lemma sg22020 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6433 sg6781

lemma sg22021 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7365

lemma sg22022 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7365

lemma sg22023 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7358

lemma sg22024 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6683

lemma sg22025 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7359

lemma sg22026 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6684

lemma sg22027 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6816

lemma sg22028 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7357

lemma sg22029 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6817

lemma sg22030 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6817

lemma sg22031 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6464 sg6703

lemma sg22032 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6177 sg7502

lemma sg22033 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7358

lemma sg22034 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6476 sg6639

lemma sg22035 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6818

lemma sg22036 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7359

lemma sg22037 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6819

lemma sg22038 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,7,7,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6819

lemma sg22039 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4344 sg11139

lemma sg22040 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6315 sg7309

lemma sg22041 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7360

lemma sg22042 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg5603 sg8412

lemma sg22043 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7310

lemma sg22044 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6472 sg6685

lemma sg22045 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg554 sg15627

lemma sg22046 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6315 sg7311

lemma sg22047 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7360

lemma sg22048 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6435 sg6778

lemma sg22049 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7361

lemma sg22050 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6300 sg7360

lemma sg22051 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6686

lemma sg22052 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7312

lemma sg22053 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6301 sg7360

lemma sg22054 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7362

lemma sg22055 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6687

lemma sg22056 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg5603 sg8413

lemma sg22057 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7314

lemma sg22058 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6435 sg6781

lemma sg22059 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7361

lemma sg22060 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6477 sg6637

lemma sg22061 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7363

lemma sg22062 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6688

lemma sg22063 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7364

lemma sg22064 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6689

lemma sg22065 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6821

lemma sg22066 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6315 sg7315

lemma sg22067 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6821

lemma sg22068 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6464 sg6704

lemma sg22069 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6316 sg7314

lemma sg22070 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6298 sg7365

lemma sg22071 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6690

lemma sg22072 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6822

lemma sg22073 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7364

lemma sg22074 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6823

lemma sg22075 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6823

lemma sg22076 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6447 sg6766

lemma sg22077 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,7,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6407 sg6825

lemma sg22078 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6299 sg7365

lemma sg22079 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,7,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6824

lemma sg22080 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,7,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6824

lemma sg22081 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,8,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5756 sg8019

lemma sg22082 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,8,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6409 sg6825

lemma sg22083 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,8,8,8,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6825

lemma sg22084 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7593

lemma sg22085 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg6151 sg7594

lemma sg22086 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,4,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7596

lemma sg22087 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7597

lemma sg22088 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg6297 sg7366

lemma sg22089 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7599

lemma sg22090 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7600

lemma sg22091 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7601

lemma sg22092 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg6414 sg6791

lemma sg22093 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7602

lemma sg22094 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7603

lemma sg22095 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7604

lemma sg22096 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg6414 sg6793

lemma sg22097 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6794

lemma sg22098 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7605

lemma sg22099 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6414 sg6795

lemma sg22100 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7606

lemma sg22101 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6303 sg7321

lemma sg22102 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6480 sg6632

lemma sg22103 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg6180 sg7492

lemma sg22104 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,5,5,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg6480 sg6633

lemma sg22105 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,4,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7607

lemma sg22106 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,4,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7608

lemma sg22107 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7609

lemma sg22108 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7367

lemma sg22109 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7610

lemma sg22110 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7611

lemma sg22111 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7612

lemma sg22112 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7368

lemma sg22113 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7369

lemma sg22114 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7613

lemma sg22115 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7614

lemma sg22116 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7370

lemma sg22117 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7615

lemma sg22118 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7371

lemma sg22119 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6650

lemma sg22120 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7616

lemma sg22121 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7372

lemma sg22122 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7373

lemma sg22123 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6652

lemma sg22124 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,5,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6653

lemma sg22125 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6176 sg7504

lemma sg22126 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7617

lemma sg22127 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7618

lemma sg22128 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6414 sg6797

lemma sg22129 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7619

lemma sg22130 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6798

lemma sg22131 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6691

lemma sg22132 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7620

lemma sg22133 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6414 sg6799

lemma sg22134 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7621

lemma sg22135 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6800

lemma sg22136 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6801

lemma sg22137 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6692

lemma sg22138 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7622

lemma sg22139 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [9,6,6,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6802

end UniversalTensorSquare
end
end

end OAI
