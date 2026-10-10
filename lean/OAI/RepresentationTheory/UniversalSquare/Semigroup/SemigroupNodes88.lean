import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes50
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes47
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes49
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes43
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes46
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes39
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes38
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes40
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes42
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes45
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes48

namespace OAI

/-! Semigroup Nodes 88. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg35741 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18372

lemma sg35742 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19786

lemma sg35743 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18942

lemma sg35744 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20862 sg15717

lemma sg35745 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18373

lemma sg35746 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17366

lemma sg35747 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19576 sg19585

lemma sg35748 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18373

lemma sg35749 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19787

lemma sg35750 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18373

lemma sg35751 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19787

lemma sg35752 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19260

lemma sg35753 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17367

lemma sg35754 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19261

lemma sg35755 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19261

lemma sg35756 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17353

lemma sg35757 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,6,6,6,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18286 sg20364

lemma sg35758 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15813

lemma sg35759 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18374

lemma sg35760 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17368

lemma sg35761 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18943

lemma sg35762 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20800 sg16162

lemma sg35763 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18374

lemma sg35764 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19788

lemma sg35765 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18374

lemma sg35766 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19788

lemma sg35767 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,5,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18943

lemma sg35768 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15804

lemma sg35769 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15814

lemma sg35770 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18915 sg19660

lemma sg35771 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17354

lemma sg35772 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18379

lemma sg35773 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18375

lemma sg35774 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18376

lemma sg35775 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18375

lemma sg35776 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19789

lemma sg35777 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18375

lemma sg35778 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19789

lemma sg35779 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18376

lemma sg35780 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19790

lemma sg35781 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18376

lemma sg35782 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19790

lemma sg35783 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18944

lemma sg35784 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16388

lemma sg35785 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18377

lemma sg35786 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15815

lemma sg35787 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18377

lemma sg35788 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19791

lemma sg35789 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18377

lemma sg35790 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19791

lemma sg35791 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19793

lemma sg35792 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18378

lemma sg35793 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17369

lemma sg35794 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18945

lemma sg35795 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18378

lemma sg35796 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19792

lemma sg35797 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18378

lemma sg35798 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19792

lemma sg35799 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18945

lemma sg35800 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17370

lemma sg35801 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19262

lemma sg35802 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18946

lemma sg35803 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18379

lemma sg35804 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19793

lemma sg35805 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18379

lemma sg35806 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19793

lemma sg35807 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18379

lemma sg35808 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19793

lemma sg35809 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17371

lemma sg35810 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19263

lemma sg35811 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19263

lemma sg35812 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17356

lemma sg35813 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18286 sg20365

lemma sg35814 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,6,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17215

lemma sg35815 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20852 sg15806

lemma sg35816 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20864 sg15716

lemma sg35817 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20865 sg15716

lemma sg35818 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18383

lemma sg35819 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18380

lemma sg35820 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15816

lemma sg35821 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18380

lemma sg35822 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19794

lemma sg35823 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18380

lemma sg35824 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19794

lemma sg35825 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16387

lemma sg35826 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18381

lemma sg35827 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17372

lemma sg35828 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18947

lemma sg35829 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18381

lemma sg35830 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19795

lemma sg35831 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18381

lemma sg35832 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19795

lemma sg35833 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18947

lemma sg35834 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17373

lemma sg35835 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19264

lemma sg35836 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19264

lemma sg35837 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18384

lemma sg35838 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15817

lemma sg35839 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19797

lemma sg35840 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18382

lemma sg35841 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17374

lemma sg35842 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19616 sg19265

lemma sg35843 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18382

lemma sg35844 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19796

lemma sg35845 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18382

lemma sg35846 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19796

lemma sg35847 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19265

lemma sg35848 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18383

lemma sg35849 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19797

lemma sg35850 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18383

lemma sg35851 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19797

lemma sg35852 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18383

lemma sg35853 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19797

lemma sg35854 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17375

lemma sg35855 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19266

lemma sg35856 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18948

lemma sg35857 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17358

lemma sg35858 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18917 sg19661

lemma sg35859 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17376

lemma sg35860 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19616 sg19267

lemma sg35861 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17376

lemma sg35862 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19267

lemma sg35863 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19267

lemma sg35864 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17359

lemma sg35865 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18917 sg19662

lemma sg35866 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17216

lemma sg35867 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18920 sg19658

lemma sg35868 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18384

lemma sg35869 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15818

lemma sg35870 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20321 sg18304

lemma sg35871 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17360

lemma sg35872 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18384

lemma sg35873 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16388

lemma sg35874 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18384

lemma sg35875 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20572

lemma sg35876 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18384

lemma sg35877 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg20528 sg17221

lemma sg35878 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17377

lemma sg35879 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19268

lemma sg35880 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19268

lemma sg35881 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17378

lemma sg35882 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19616 sg19269

lemma sg35883 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17378

lemma sg35884 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19269

lemma sg35885 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19269

lemma sg35886 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17361

lemma sg35887 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18917 sg19663

lemma sg35888 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17218

lemma sg35889 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18050

lemma sg35890 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16795

lemma sg35891 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20528 sg17223

lemma sg35892 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17362

lemma sg35893 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18113 sg20480

lemma sg35894 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17219

lemma sg35895 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20639 sg16691

lemma sg35896 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20640 sg16691

lemma sg35897 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20641 sg16691

lemma sg35898 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,7,7,7,7,7,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20531 sg17220

lemma sg35899 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,5,5,5,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18385

lemma sg35900 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,5,5,5,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20867 sg15714

lemma sg35901 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,5,5,5,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18385

lemma sg35902 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,5,5,5,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19798

lemma sg35903 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,5,5,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18385

lemma sg35904 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,5,5,5,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19798

lemma sg35905 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15819

lemma sg35906 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18386

lemma sg35907 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17379

lemma sg35908 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18949

lemma sg35909 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20855 sg15803

lemma sg35910 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18386

lemma sg35911 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19799

lemma sg35912 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18386

lemma sg35913 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19799

lemma sg35914 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,5,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18949

lemma sg35915 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20858 sg15720

lemma sg35916 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15820

lemma sg35917 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20859 sg15720

lemma sg35918 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20860 sg15720

lemma sg35919 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18391

lemma sg35920 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18387

lemma sg35921 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18388

lemma sg35922 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18387

lemma sg35923 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19800

lemma sg35924 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18387

lemma sg35925 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19800

lemma sg35926 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18388

lemma sg35927 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19801

lemma sg35928 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18388

lemma sg35929 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19801

lemma sg35930 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18950

lemma sg35931 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20702 sg16272

lemma sg35932 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18389

lemma sg35933 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15821

lemma sg35934 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18389

lemma sg35935 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19802

lemma sg35936 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18389

lemma sg35937 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19802

lemma sg35938 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18391

lemma sg35939 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18390

lemma sg35940 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17380

lemma sg35941 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18951

lemma sg35942 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18390

lemma sg35943 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19803

lemma sg35944 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18390

lemma sg35945 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19803

lemma sg35946 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18951

lemma sg35947 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17381

lemma sg35948 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19270

lemma sg35949 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18952

lemma sg35950 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18391

lemma sg35951 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg16649 sg20675

lemma sg35952 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18391

lemma sg35953 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20573

lemma sg35954 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18391

lemma sg35955 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg16650 sg20675

lemma sg35956 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17382

lemma sg35957 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19271

lemma sg35958 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19271

lemma sg35959 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17224

lemma sg35960 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20530 sg17224

lemma sg35961 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,6,6,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17353

lemma sg35962 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20858 sg15721

lemma sg35963 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15822

lemma sg35964 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20859 sg15721

lemma sg35965 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20860 sg15721

lemma sg35966 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16390

lemma sg35967 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18392

lemma sg35968 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18393

lemma sg35969 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18392

lemma sg35970 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19804

lemma sg35971 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18392

lemma sg35972 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19804

lemma sg35973 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18393

lemma sg35974 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19805

lemma sg35975 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18393

lemma sg35976 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19805

lemma sg35977 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,5,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18953

lemma sg35978 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20858 sg15722

lemma sg35979 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18203

lemma sg35980 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17354

lemma sg35981 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18397

lemma sg35982 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18394

lemma sg35983 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15823

lemma sg35984 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18394

lemma sg35985 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19806

lemma sg35986 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18394

lemma sg35987 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19806

lemma sg35988 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20686 sg16390

lemma sg35989 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18395

lemma sg35990 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17383

lemma sg35991 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18954

lemma sg35992 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18395

lemma sg35993 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19807

lemma sg35994 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18395

lemma sg35995 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19807

lemma sg35996 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18954

lemma sg35997 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17384

lemma sg35998 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19272

lemma sg35999 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18955

lemma sg36000 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16392

lemma sg36001 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15824

lemma sg36002 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19809

lemma sg36003 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18396

lemma sg36004 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17385

lemma sg36005 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19576 sg19586

lemma sg36006 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18396

lemma sg36007 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19808

lemma sg36008 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18396

lemma sg36009 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19808

lemma sg36010 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19273

lemma sg36011 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18397

lemma sg36012 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19809

lemma sg36013 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18397

lemma sg36014 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19809

lemma sg36015 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18397

lemma sg36016 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19809

lemma sg36017 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17386

lemma sg36018 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19274

lemma sg36019 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18956

lemma sg36020 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17225

lemma sg36021 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20530 sg17225

lemma sg36022 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17387

lemma sg36023 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19576 sg19587

lemma sg36024 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17387

lemma sg36025 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19275

lemma sg36026 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19275

lemma sg36027 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17226

lemma sg36028 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20530 sg17226

lemma sg36029 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,6,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17356

lemma sg36030 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18400

lemma sg36031 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18398

lemma sg36032 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20858 sg15723

lemma sg36033 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18398

lemma sg36034 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19810

lemma sg36035 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18398

lemma sg36036 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19810

lemma sg36037 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18401

lemma sg36038 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15826

lemma sg36039 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19812

lemma sg36040 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18399

lemma sg36041 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17388

lemma sg36042 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18957

lemma sg36043 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18399

lemma sg36044 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19811

lemma sg36045 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18399

lemma sg36046 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19811

lemma sg36047 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18957

lemma sg36048 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18400

lemma sg36049 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19812

lemma sg36050 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18400

lemma sg36051 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19812

lemma sg36052 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18400

lemma sg36053 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19812

lemma sg36054 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17389

lemma sg36055 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19276

lemma sg36056 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18958

lemma sg36057 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17227

lemma sg36058 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20530 sg17227

lemma sg36059 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18402

lemma sg36060 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19813

lemma sg36061 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15827

lemma sg36062 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20859 sg15724

lemma sg36063 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20860 sg15724

lemma sg36064 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18401

lemma sg36065 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19813

lemma sg36066 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18401

lemma sg36067 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19813

lemma sg36068 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18401

lemma sg36069 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19813

lemma sg36070 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17390

lemma sg36071 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19277

lemma sg36072 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18959

lemma sg36073 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17391

lemma sg36074 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18960

lemma sg36075 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17391

lemma sg36076 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19278

lemma sg36077 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18960

lemma sg36078 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17228

lemma sg36079 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20530 sg17228

lemma sg36080 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17358

lemma sg36081 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20637 sg16693

lemma sg36082 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20638 sg16693

lemma sg36083 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20528 sg17229

lemma sg36084 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17229

lemma sg36085 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20530 sg17229

lemma sg36086 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17359

lemma sg36087 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17699

lemma sg36088 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18402

lemma sg36089 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20501 sg17392

lemma sg36090 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18402

lemma sg36091 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20687 sg16392

lemma sg36092 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18112 sg20492

lemma sg36093 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18402

lemma sg36094 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20574

lemma sg36095 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18402

lemma sg36096 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17360

lemma sg36097 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20632 sg16800

lemma sg36098 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17392

lemma sg36099 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19616 sg19279

lemma sg36100 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19279

lemma sg36101 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17392

lemma sg36102 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19279

lemma sg36103 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19619 sg19279

lemma sg36104 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17230

lemma sg36105 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20530 sg17230

lemma sg36106 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20637 sg16694

lemma sg36107 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20638 sg16694

lemma sg36108 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20528 sg17231

lemma sg36109 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20529 sg17231

lemma sg36110 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20530 sg17231

lemma sg36111 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17361

lemma sg36112 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16795

lemma sg36113 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17362

lemma sg36114 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16795

lemma sg36115 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17362

lemma sg36116 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,7,7,7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20642 sg16691

lemma sg36117 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,4,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20886 sg15700

lemma sg36118 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20858 sg15725

lemma sg36119 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20887 sg15700

lemma sg36120 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg20888 sg15700

lemma sg36121 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20685 sg16393

lemma sg36122 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18403

lemma sg36123 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg15828

lemma sg36124 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18403

lemma sg36125 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19814

lemma sg36126 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18403

lemma sg36127 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19814

lemma sg36128 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20857 sg15728

lemma sg36129 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18404

lemma sg36130 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20502 sg17393

lemma sg36131 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg19621 sg18961

lemma sg36132 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18404

lemma sg36133 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19815

lemma sg36134 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18404

lemma sg36135 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19815

lemma sg36136 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18961

lemma sg36137 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20503 sg17394

lemma sg36138 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg19618 sg19280

lemma sg36139 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,5,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg19622 sg18962

lemma sg36140 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,8,8,8,6,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18407

end UniversalTensorSquare
end
end

end OAI
