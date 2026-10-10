import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupLeaves3
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupLeaves4
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupLeaves5
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes0

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg696 : RowSquare [6,2,1] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg89

lemma sg697 : RowSquare [6,2,1] [4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg74

lemma sg698 : RowSquare [6,2,1] [4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg32

lemma sg699 : RowSquare [6,2,1] [4,3,1,1] := by
  exact rowSquare_join (by decide) sg17 sg33

lemma sg700 : RowSquare [6,2,1] [4,3,2] := by
  exact rowSquare_join (by decide) sg16 sg34

lemma sg701 : RowSquare [6,2,1] [4,4,1] := by
  exact rowSquare_join (by decide) sg17 sg34

lemma sg702 : RowSquare [6,2,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg32

lemma sg703 : RowSquare [6,2,1] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg36

lemma sg704 : RowSquare [6,2,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg26

lemma sg705 : RowSquare [6,2,1] [8,1] := by
  exact rowSquare_join (by decide) sg18 sg38

lemma sg706 : RowSquare [6,3] [3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg97

lemma sg707 : RowSquare [6,3] [4,4,1] := by
  exact rowSquare_join (by decide) sg17 sg40

lemma sg708 : RowSquare [7,1,1] [5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg32

lemma sg709 : RowSquare [7,1,1] [5,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg88

lemma sg710 : RowSquare [7,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg7 sg89

lemma sg711 : RowSquare [7,1,1] [6,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg33

lemma sg712 : RowSquare [7,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg20 sg34

lemma sg713 : RowSquare [7,1,1] [6,3] := by
  exact rowSquare_join (by decide) sg7 sg92

lemma sg714 : RowSquare [7,2] [5,3,1] := by
  exact rowSquare_join (by decide) sg16 sg46

lemma sg715 : RowSquare [7,2] [5,4] := by
  exact rowSquare_join (by decide) sg17 sg46

lemma sg716 : RowSquare [8,1] [7,1,1] := by
  exact rowSquare_join (by decide) sg16 sg49

lemma sg717 : RowSquare [8,1] [7,2] := by
  exact rowSquare_join (by decide) sg17 sg49

lemma sg719 : RowSquare [2,1,1,1,1,1,1,1,1] [8,2] := by
  exact rowSquare_join (by decide) sg46 sg49

lemma sg721 : RowSquare [2,2,1,1,1,1,1,1] [6,2,2] := by
  exact rowSquare_join (by decide) sg45 sg45

lemma sg722 : RowSquare [2,2,1,1,1,1,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg46 sg46

lemma sg723 : RowSquare [2,2,1,1,1,1,1,1] [7,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg49

lemma sg724 : RowSquare [2,2,1,1,1,1,1,1] [7,3] := by
  exact rowSquare_join (by decide) sg46 sg47

lemma sg725 : RowSquare [2,2,1,1,1,1,1,1] [8,2] := by
  exact rowSquare_join (by decide) sg46 sg48

lemma sg726 : RowSquare [2,2,1,1,1,1,1,1] [9,1] := by
  exact rowSquare_join (by decide) sg47 sg48

lemma sg727 : RowSquare [2,2,2,1,1,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg46 sg42

lemma sg728 : RowSquare [2,2,2,1,1,1,1] [7,3] := by
  exact rowSquare_join (by decide) sg46 sg43

lemma sg729 : RowSquare [2,2,2,1,1,1,1] [8,2] := by
  exact rowSquare_join (by decide) sg46 sg44

lemma sg731 : RowSquare [3,1,1,1,1,1,1,1] [6,2,2] := by
  exact rowSquare_join (by decide) sg20 sg89

lemma sg732 : RowSquare [3,1,1,1,1,1,1,1] [7,2,1] := by
  exact rowSquare_join (by decide) sg34 sg49

lemma sg733 : RowSquare [3,1,1,1,1,1,1,1] [7,3] := by
  exact rowSquare_join (by decide) sg20 sg92

lemma sg734 : RowSquare [3,1,1,1,1,1,1,1] [8,2] := by
  exact rowSquare_join (by decide) sg0 sg429

lemma sg735 : RowSquare [3,2,1,1,1,1,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg45

lemma sg736 : RowSquare [3,2,1,1,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg390

lemma sg737 : RowSquare [3,2,1,1,1,1,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg46

lemma sg738 : RowSquare [3,2,1,1,1,1,1] [4,3,2,1] := by
  exact rowSquare_join (by decide) sg16 sg88

lemma sg739 : RowSquare [3,2,1,1,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg16 sg89

lemma sg740 : RowSquare [3,2,1,1,1,1,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg17 sg88

lemma sg741 : RowSquare [3,2,1,1,1,1,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg89

lemma sg742 : RowSquare [3,2,1,1,1,1,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg74

lemma sg743 : RowSquare [3,2,1,1,1,1,1] [5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg47

lemma sg744 : RowSquare [3,2,1,1,1,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg33 sg45

lemma sg745 : RowSquare [3,2,1,1,1,1,1] [5,3,1,1] := by
  exact rowSquare_join (by decide) sg33 sg46

lemma sg746 : RowSquare [3,2,1,1,1,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg34 sg45

lemma sg747 : RowSquare [3,2,1,1,1,1,1] [5,4,1] := by
  exact rowSquare_join (by decide) sg34 sg46

lemma sg748 : RowSquare [3,2,1,1,1,1,1] [5,5] := by
  exact rowSquare_join (by decide) sg17 sg92

lemma sg749 : RowSquare [3,2,1,1,1,1,1] [6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg48

lemma sg750 : RowSquare [3,2,1,1,1,1,1] [6,2,1,1] := by
  exact rowSquare_join (by decide) sg33 sg47

lemma sg751 : RowSquare [3,2,2,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg39

lemma sg752 : RowSquare [3,2,2,1,1,1] [3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg74

lemma sg753 : RowSquare [3,2,2,1,1,1] [3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg40

lemma sg754 : RowSquare [3,2,2,1,1,1] [3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg88

lemma sg755 : RowSquare [3,2,2,1,1,1] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg89

lemma sg756 : RowSquare [3,2,2,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg0 sg440

lemma sg758 : RowSquare [3,2,2,2,1] [2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg74

lemma sg760 : RowSquare [3,2,2,2,1] [3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg74

lemma sg761 : RowSquare [3,2,2,2,1] [5,5] := by
  exact rowSquare_join (by decide) sg14 sg80

lemma sg762 : RowSquare [3,3,1,1,1,1] [2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg32

lemma sg763 : RowSquare [3,3,1,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg636

lemma sg764 : RowSquare [3,3,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg33

lemma sg766 : RowSquare [3,3,1,1,1,1] [3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg34

lemma sg769 : RowSquare [3,3,1,1,1,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg348

lemma sg770 : RowSquare [3,3,1,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg33 sg33

lemma sg771 : RowSquare [3,3,1,1,1,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg36

lemma sg772 : RowSquare [3,3,1,1,1,1] [4,3,2,1] := by
  exact rowSquare_join (by decide) sg33 sg34

lemma sg773 : RowSquare [3,3,1,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg9 sg89

lemma sg774 : RowSquare [3,3,1,1,1,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg10 sg88

lemma sg775 : RowSquare [3,3,1,1,1,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg34 sg34

lemma sg776 : RowSquare [3,3,1,1,1,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg154

lemma sg777 : RowSquare [3,3,1,1,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg33 sg35

lemma sg778 : RowSquare [3,3,1,1,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg34 sg35

lemma sg779 : RowSquare [3,3,1,1,1,1] [5,4,1] := by
  exact rowSquare_join (by decide) sg34 sg36

lemma sg780 : RowSquare [3,3,1,1,1,1] [5,5] := by
  exact rowSquare_join (by decide) sg10 sg92

lemma sg781 : RowSquare [3,3,1,1,1,1] [6,2,2] := by
  exact rowSquare_join (by decide) sg1 sg239

lemma sg782 : RowSquare [3,3,1,1,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg1 sg241

lemma sg783 : RowSquare [3,3,1,1,1,1] [7,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg50

lemma sg784 : RowSquare [3,3,1,1,1,1] [7,2,1] := by
  exact rowSquare_join (by decide) sg1 sg243

lemma sg785 : RowSquare [3,3,1,1,1,1] [7,3] := by
  exact rowSquare_join (by decide) sg1 sg244

lemma sg786 : RowSquare [3,3,1,1,1,1] [8,1,1] := by
  exact rowSquare_join (by decide) sg1 sg245

lemma sg787 : RowSquare [3,3,1,1,1,1] [8,2] := by
  exact rowSquare_join (by decide) sg14 sg50

lemma sg788 : RowSquare [3,3,1,1,1,1] [9,1] := by
  exact rowSquare_join (by decide) sg1 sg247

lemma sg793 : RowSquare [3,3,2,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg306

lemma sg794 : RowSquare [3,3,2,1,1] [3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg74

lemma sg795 : RowSquare [3,3,2,1,1] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg156

lemma sg797 : RowSquare [3,3,2,2] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg306

lemma sg798 : RowSquare [3,3,3,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg516

lemma sg799 : RowSquare [4,1,1,1,1,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg178

lemma sg800 : RowSquare [4,1,1,1,1,1,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg371

lemma sg801 : RowSquare [4,1,1,1,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg373

lemma sg802 : RowSquare [4,1,1,1,1,1,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg179

lemma sg803 : RowSquare [4,1,1,1,1,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg7 sg181

lemma sg804 : RowSquare [4,1,1,1,1,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg2 sg378

lemma sg805 : RowSquare [4,1,1,1,1,1,1] [6,3,1] := by
  exact rowSquare_join (by decide) sg7 sg185

lemma sg806 : RowSquare [4,1,1,1,1,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg2 sg383

lemma sg807 : RowSquare [4,2,1,1,1,1] [2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg178

lemma sg810 : RowSquare [4,2,1,1,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg330

lemma sg811 : RowSquare [4,2,1,1,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg178

lemma sg812 : RowSquare [4,2,1,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg179

lemma sg813 : RowSquare [4,2,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg616

lemma sg815 : RowSquare [4,2,1,1,1,1] [3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg180

lemma sg817 : RowSquare [4,2,1,1,1,1] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg181

lemma sg818 : RowSquare [4,2,1,1,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg178

lemma sg819 : RowSquare [4,2,1,1,1,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg179

lemma sg820 : RowSquare [4,2,1,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg456

lemma sg821 : RowSquare [4,2,1,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg0 sg459

lemma sg822 : RowSquare [4,2,1,1,1,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg17 sg67

lemma sg823 : RowSquare [4,2,1,1,1,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg68

lemma sg824 : RowSquare [4,2,1,1,1,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg460

lemma sg825 : RowSquare [4,2,1,1,1,1] [5,5] := by
  exact rowSquare_join (by decide) sg17 sg71

lemma sg830 : RowSquare [4,2,2,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg330

lemma sg831 : RowSquare [4,2,2,1,1] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg68

lemma sg842 : RowSquare [4,3,1,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg548

lemma sg843 : RowSquare [4,3,1,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg549

lemma sg844 : RowSquare [4,3,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg489

lemma sg845 : RowSquare [4,3,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg490

lemma sg848 : RowSquare [4,3,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg114

lemma sg872 : RowSquare [4,3,3] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg516

lemma sg882 : RowSquare [4,4,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg480

lemma sg883 : RowSquare [4,4,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg481

lemma sg888 : RowSquare [5,1,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

lemma sg893 : RowSquare [5,1,1,1,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg587

lemma sg894 : RowSquare [5,1,1,1,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg588

lemma sg895 : RowSquare [5,1,1,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg589

lemma sg896 : RowSquare [5,1,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

lemma sg900 : RowSquare [5,1,1,1,1,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg595

lemma sg901 : RowSquare [5,1,1,1,1,1] [4,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg596

lemma sg904 : RowSquare [5,1,1,1,1,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg521

lemma sg905 : RowSquare [5,1,1,1,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg523

lemma sg906 : RowSquare [5,1,1,1,1,1] [5,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg524

lemma sg907 : RowSquare [5,1,1,1,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg0 sg525

lemma sg908 : RowSquare [5,1,1,1,1,1] [5,4,1] := by
  exact rowSquare_join (by decide) sg0 sg602

lemma sg911 : RowSquare [5,2,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg47 sg21

lemma sg912 : RowSquare [5,2,1,1,1] [2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg21

lemma sg913 : RowSquare [5,2,1,1,1] [2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg53

lemma sg914 : RowSquare [5,2,1,1,1] [2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg52

lemma sg916 : RowSquare [5,2,1,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg534

lemma sg917 : RowSquare [5,2,1,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg535

lemma sg918 : RowSquare [5,2,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg536

lemma sg919 : RowSquare [5,2,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg537

lemma sg920 : RowSquare [5,2,1,1,1] [3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg51

lemma sg921 : RowSquare [5,2,1,1,1] [3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg136

lemma sg923 : RowSquare [5,2,1,1,1] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg134

lemma sg924 : RowSquare [5,2,1,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg312

lemma sg925 : RowSquare [5,2,1,1,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg313

lemma sg926 : RowSquare [5,2,1,1,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg132

lemma sg927 : RowSquare [5,2,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg271

lemma sg928 : RowSquare [5,2,1,1,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg541

lemma sg929 : RowSquare [5,2,1,1,1] [4,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg133

lemma sg930 : RowSquare [5,2,1,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg134

lemma sg931 : RowSquare [5,2,1,1,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg2 sg271

lemma sg933 : RowSquare [5,2,1,1,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg272

lemma sg934 : RowSquare [5,2,1,1,1] [5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg132

lemma sg935 : RowSquare [5,2,1,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg135

lemma sg936 : RowSquare [5,2,1,1,1] [5,3,1,1] := by
  exact rowSquare_join (by decide) sg5 sg133

lemma sg937 : RowSquare [5,2,1,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg4 sg136

lemma sg938 : RowSquare [5,2,1,1,1] [5,4,1] := by
  exact rowSquare_join (by decide) sg4 sg137

lemma sg944 : RowSquare [5,2,2,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg548

lemma sg945 : RowSquare [5,2,2,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg549

lemma sg946 : RowSquare [5,2,2,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg550

lemma sg947 : RowSquare [5,2,2,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg551

lemma sg952 : RowSquare [5,2,2,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg178

lemma sg953 : RowSquare [5,2,2,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg285

lemma sg954 : RowSquare [5,2,2,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg22

lemma sg955 : RowSquare [5,2,2,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg287

lemma sg956 : RowSquare [5,2,2,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg10 sg67

lemma sg957 : RowSquare [5,2,2,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg10 sg68

lemma sg962 : RowSquare [5,3,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg330

lemma sg963 : RowSquare [5,3,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg562

lemma sg965 : RowSquare [5,3,1,1] [3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg67

lemma sg966 : RowSquare [5,3,1,1] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg68

lemma sg967 : RowSquare [5,3,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg331

lemma sg968 : RowSquare [5,3,1,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg145

lemma sg969 : RowSquare [5,3,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg69

lemma sg970 : RowSquare [5,3,1,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg66

lemma sg971 : RowSquare [5,3,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg16 sg55

lemma sg972 : RowSquare [5,3,1,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg71

lemma sg973 : RowSquare [5,3,1,1] [5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg145

lemma sg974 : RowSquare [5,3,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg22

lemma sg978 : RowSquare [5,3,2] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg306

lemma sg979 : RowSquare [5,3,2] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg26

lemma sg980 : RowSquare [5,3,2] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg156

lemma sg981 : RowSquare [5,4,1] [2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg74

lemma sg983 : RowSquare [5,4,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg165

lemma sg984 : RowSquare [5,4,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg75

lemma sg985 : RowSquare [5,4,1] [3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg74

lemma sg986 : RowSquare [5,4,1] [3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg76

lemma sg987 : RowSquare [5,4,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg165

lemma sg988 : RowSquare [5,4,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg168

lemma sg989 : RowSquare [5,4,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg75

lemma sg990 : RowSquare [5,4,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg80

lemma sg991 : RowSquare [5,4,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg74

lemma sg992 : RowSquare [5,4,1] [5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg168

lemma sg993 : RowSquare [5,4,1] [5,5] := by
  exact rowSquare_join (by decide) sg14 sg80

lemma sg994 : RowSquare [5,4,1] [6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg75

lemma sg995 : RowSquare [5,5] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg84

lemma sg997 : RowSquare [6,1,1,1,1] [2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg586

lemma sg1002 : RowSquare [6,1,1,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg587

lemma sg1003 : RowSquare [6,1,1,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg588

lemma sg1004 : RowSquare [6,1,1,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg589

lemma sg1005 : RowSquare [6,1,1,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg590

lemma sg1009 : RowSquare [6,1,1,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg312

lemma sg1010 : RowSquare [6,1,1,1,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg313

lemma sg1011 : RowSquare [6,1,1,1,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg314

lemma sg1012 : RowSquare [6,1,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg315

lemma sg1013 : RowSquare [6,1,1,1,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg595

lemma sg1014 : RowSquare [6,1,1,1,1] [4,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg596

lemma sg1017 : RowSquare [6,1,1,1,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg316

lemma sg1018 : RowSquare [6,1,1,1,1] [5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg317

lemma sg1019 : RowSquare [6,1,1,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg318

lemma sg1020 : RowSquare [6,1,1,1,1] [5,3,1,1] := by
  exact rowSquare_join (by decide) sg2 sg319

lemma sg1021 : RowSquare [6,1,1,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg2 sg320

lemma sg1022 : RowSquare [6,1,1,1,1] [5,4,1] := by
  exact rowSquare_join (by decide) sg0 sg602

lemma sg1024 : RowSquare [6,1,1,1,1] [6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg132

lemma sg1025 : RowSquare [6,1,1,1,1] [6,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg133

lemma sg1026 : RowSquare [6,1,1,1,1] [6,2,2] := by
  exact rowSquare_join (by decide) sg7 sg134

lemma sg1027 : RowSquare [6,1,1,1,1] [6,3,1] := by
  exact rowSquare_join (by decide) sg2 sg323

lemma sg1028 : RowSquare [6,1,1,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg2 sg324

lemma sg1029 : RowSquare [6,1,1,1,1] [7,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg135

lemma sg1030 : RowSquare [6,1,1,1,1] [7,3] := by
  exact rowSquare_join (by decide) sg7 sg137

lemma sg1031 : RowSquare [6,2,1,1] [2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg178

lemma sg1034 : RowSquare [6,2,1,1] [3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg330

lemma sg1035 : RowSquare [6,2,1,1] [3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg178

lemma sg1036 : RowSquare [6,2,1,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg179

lemma sg1037 : RowSquare [6,2,1,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg616

lemma sg1039 : RowSquare [6,2,1,1] [3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg180

lemma sg1041 : RowSquare [6,2,1,1] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg181

lemma sg1042 : RowSquare [6,2,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg178

lemma sg1043 : RowSquare [6,2,1,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg179

lemma sg1044 : RowSquare [6,2,1,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg16 sg66

lemma sg1045 : RowSquare [6,2,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg334

lemma sg1046 : RowSquare [6,2,1,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg66

lemma sg1047 : RowSquare [6,2,1,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg16 sg68

lemma sg1048 : RowSquare [6,2,1,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg17 sg67

lemma sg1049 : RowSquare [6,2,1,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg68

lemma sg1050 : RowSquare [6,2,1,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg142

lemma sg1051 : RowSquare [6,2,1,1] [5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg66

lemma sg1052 : RowSquare [6,2,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg16 sg69

lemma sg1053 : RowSquare [6,2,1,1] [5,3,1,1] := by
  exact rowSquare_join (by decide) sg17 sg69

lemma sg1054 : RowSquare [6,2,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg16 sg70

lemma sg1055 : RowSquare [6,2,1,1] [5,4,1] := by
  exact rowSquare_join (by decide) sg16 sg71

lemma sg1056 : RowSquare [6,2,1,1] [5,5] := by
  exact rowSquare_join (by decide) sg17 sg71

lemma sg1057 : RowSquare [6,2,1,1] [6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg66

lemma sg1058 : RowSquare [6,2,1,1] [6,2,1,1] := by
  exact rowSquare_join (by decide) sg18 sg69

lemma sg1059 : RowSquare [6,2,1,1] [6,2,2] := by
  exact rowSquare_join (by decide) sg45 sg22

lemma sg1060 : RowSquare [6,2,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg46 sg23

lemma sg1061 : RowSquare [6,2,2] [2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg32

lemma sg1062 : RowSquare [6,2,2] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg636

lemma sg1066 : RowSquare [6,2,2] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg10 sg88

lemma sg1067 : RowSquare [6,2,2] [5,5] := by
  exact rowSquare_join (by decide) sg10 sg92

lemma sg1068 : RowSquare [6,3,1] [3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg74

lemma sg1069 : RowSquare [6,3,1] [3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg39

lemma sg1070 : RowSquare [6,3,1] [3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg74

lemma sg1071 : RowSquare [6,3,1] [3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg40

lemma sg1072 : RowSquare [6,3,1] [3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg88

lemma sg1073 : RowSquare [6,3,1] [3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg89

lemma sg1074 : RowSquare [6,3,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg74

lemma sg1092 : RowSquare [7,1,1,1] [4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg178

lemma sg1093 : RowSquare [7,1,1,1] [4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg371

lemma sg1094 : RowSquare [7,1,1,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg372

lemma sg1095 : RowSquare [7,1,1,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg373

lemma sg1096 : RowSquare [7,1,1,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg179

lemma sg1097 : RowSquare [7,1,1,1] [5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg180

lemma sg1098 : RowSquare [7,1,1,1] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg7 sg181

lemma sg1099 : RowSquare [7,1,1,1] [5,3,1,1] := by
  exact rowSquare_join (by decide) sg2 sg377

lemma sg1100 : RowSquare [7,1,1,1] [5,3,2] := by
  exact rowSquare_join (by decide) sg2 sg378

lemma sg1101 : RowSquare [7,1,1,1] [6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg66

lemma sg1102 : RowSquare [7,1,1,1] [6,2,2] := by
  exact rowSquare_join (by decide) sg20 sg68

lemma sg1103 : RowSquare [7,1,1,1] [6,4] := by
  exact rowSquare_join (by decide) sg2 sg383

lemma sg1104 : RowSquare [7,2,1] [4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg45

lemma sg1105 : RowSquare [7,2,1] [4,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg390

lemma sg1106 : RowSquare [7,2,1] [4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg46

lemma sg1107 : RowSquare [7,2,1] [4,3,2,1] := by
  exact rowSquare_join (by decide) sg16 sg88

lemma sg1108 : RowSquare [7,2,1] [4,3,3] := by
  exact rowSquare_join (by decide) sg16 sg89

lemma sg1109 : RowSquare [7,2,1] [4,4,1,1] := by
  exact rowSquare_join (by decide) sg17 sg88

lemma sg1110 : RowSquare [7,2,1] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg89

lemma sg1111 : RowSquare [7,2,1] [5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg74

lemma sg1112 : RowSquare [7,2,1] [5,5] := by
  exact rowSquare_join (by decide) sg17 sg92

lemma sg1113 : RowSquare [7,2,1] [9,1] := by
  exact rowSquare_join (by decide) sg47 sg38

lemma sg1114 : RowSquare [7,3] [4,3,3] := by
  exact rowSquare_join (by decide) sg16 sg97

lemma sg1115 : RowSquare [7,3] [4,4,2] := by
  exact rowSquare_join (by decide) sg17 sg97

lemma sg1116 : RowSquare [7,3] [5,2,2,1] := by
  exact rowSquare_join (by decide) sg39 sg45

lemma sg1117 : RowSquare [7,3] [5,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg46

lemma sg1118 : RowSquare [7,3] [5,3,2] := by
  exact rowSquare_join (by decide) sg40 sg45

lemma sg1119 : RowSquare [7,3] [5,4,1] := by
  exact rowSquare_join (by decide) sg40 sg46

lemma sg1120 : RowSquare [2,1,1,1,1,1,1,1,1,1] [9,2] := by
  exact rowSquare_join (by decide) sg46 sg108

lemma sg1121 : RowSquare [2,2,1,1,1,1,1,1,1] [7,2,2] := by
  exact rowSquare_join (by decide) sg45 sg104

lemma sg1122 : RowSquare [2,2,1,1,1,1,1,1,1] [7,4] := by
  exact rowSquare_join (by decide) sg46 sg105

lemma sg1123 : RowSquare [2,2,1,1,1,1,1,1,1] [8,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg108

lemma sg1124 : RowSquare [2,2,1,1,1,1,1,1,1] [8,3] := by
  exact rowSquare_join (by decide) sg46 sg106

lemma sg1125 : RowSquare [2,2,1,1,1,1,1,1,1] [9,2] := by
  exact rowSquare_join (by decide) sg46 sg107

lemma sg1126 : RowSquare [2,2,1,1,1,1,1,1,1] [10,1] := by
  exact rowSquare_join (by decide) sg47 sg107

lemma sg1127 : RowSquare [2,2,2,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg17 sg230

lemma sg1128 : RowSquare [2,2,2,1,1,1,1,1] [7,4] := by
  exact rowSquare_join (by decide) sg46 sg101

lemma sg1129 : RowSquare [2,2,2,1,1,1,1,1] [9,2] := by
  exact rowSquare_join (by decide) sg46 sg103

lemma sg1130 : RowSquare [2,2,2,2,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg17 sg213

lemma sg1136 : RowSquare [3,1,1,1,1,1,1,1,1] [8,3] := by
  exact rowSquare_join (by decide) sg49 sg92

lemma sg1137 : RowSquare [3,2,1,1,1,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg390

lemma sg1138 : RowSquare [3,2,1,1,1,1,1,1] [5,3,3] := by
  exact rowSquare_join (by decide) sg45 sg89

lemma sg1139 : RowSquare [3,2,1,1,1,1,1,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg46 sg89

lemma sg1140 : RowSquare [3,2,1,1,1,1,1,1] [6,4,1] := by
  exact rowSquare_join (by decide) sg34 sg105

lemma sg1141 : RowSquare [3,2,1,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg92

lemma sg1142 : RowSquare [3,2,2,1,1,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg89

lemma sg1143 : RowSquare [3,2,2,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg46 sg80

lemma sg1144 : RowSquare [3,2,2,2,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg83

lemma sg1145 : RowSquare [3,2,2,2,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg195

lemma sg1146 : RowSquare [3,3,1,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg87

lemma sg1147 : RowSquare [3,3,1,1,1,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg88

lemma sg1148 : RowSquare [3,3,1,1,1,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg89

lemma sg1149 : RowSquare [3,3,1,1,1,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg636

lemma sg1150 : RowSquare [3,3,1,1,1,1,1] [4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg90

lemma sg1151 : RowSquare [3,3,1,1,1,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1063

lemma sg1152 : RowSquare [3,3,1,1,1,1,1] [4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg91

lemma sg1153 : RowSquare [3,3,1,1,1,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg33 sg88

lemma sg1154 : RowSquare [3,3,1,1,1,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg33 sg89

lemma sg1155 : RowSquare [3,3,1,1,1,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg92

lemma sg1156 : RowSquare [3,3,1,1,1,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg34 sg88

lemma sg1157 : RowSquare [3,3,1,1,1,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg34 sg89

lemma sg1158 : RowSquare [3,3,1,1,1,1,1] [5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg348

lemma sg1159 : RowSquare [3,3,1,1,1,1,1] [5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg93

lemma sg1160 : RowSquare [3,3,1,1,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg33 sg90

lemma sg1161 : RowSquare [3,3,1,1,1,1,1] [5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg94

lemma sg1162 : RowSquare [3,3,1,1,1,1,1] [5,3,3] := by
  exact rowSquare_join (by decide) sg35 sg89

lemma sg1163 : RowSquare [3,3,1,1,1,1,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg34 sg91

lemma sg1164 : RowSquare [3,3,1,1,1,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg34 sg92

lemma sg1165 : RowSquare [3,3,1,1,1,1,1] [6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg154

lemma sg1166 : RowSquare [3,3,1,1,1,1,1] [6,2,2,1] := by
  exact rowSquare_join (by decide) sg33 sg93

lemma sg1167 : RowSquare [3,3,1,1,1,1,1] [6,3,2] := by
  exact rowSquare_join (by decide) sg34 sg93

lemma sg1168 : RowSquare [3,3,1,1,1,1,1] [6,4,1] := by
  exact rowSquare_join (by decide) sg34 sg94

lemma sg1169 : RowSquare [3,3,1,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg36 sg92

lemma sg1170 : RowSquare [3,3,1,1,1,1,1] [7,2,2] := by
  exact rowSquare_join (by decide) sg1 sg432

lemma sg1171 : RowSquare [3,3,1,1,1,1,1] [7,3,1] := by
  exact rowSquare_join (by decide) sg1 sg433

lemma sg1172 : RowSquare [3,3,1,1,1,1,1] [7,4] := by
  exact rowSquare_join (by decide) sg1 sg434

lemma sg1173 : RowSquare [3,3,1,1,1,1,1] [8,2,1] := by
  exact rowSquare_join (by decide) sg1 sg436

lemma sg1174 : RowSquare [3,3,1,1,1,1,1] [8,3] := by
  exact rowSquare_join (by decide) sg1 sg437

lemma sg1175 : RowSquare [3,3,1,1,1,1,1] [9,2] := by
  exact rowSquare_join (by decide) sg14 sg109

lemma sg1176 : RowSquare [3,3,1,1,1,1,1] [10,1] := by
  exact rowSquare_join (by decide) sg1 sg439

lemma sg1178 : RowSquare [3,3,2,1,1,1] [2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg74

lemma sg1179 : RowSquare [3,3,2,1,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg76

lemma sg1181 : RowSquare [3,3,3,2] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg516

lemma sg1182 : RowSquare [4,1,1,1,1,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg7 sg373

lemma sg1183 : RowSquare [4,1,1,1,1,1,1,1] [6,3,2] := by
  exact rowSquare_join (by decide) sg7 sg378

lemma sg1184 : RowSquare [4,1,1,1,1,1,1,1] [7,4] := by
  exact rowSquare_join (by decide) sg7 sg383

lemma sg1185 : RowSquare [4,2,1,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg178

lemma sg1186 : RowSquare [4,2,1,1,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg1032

lemma sg1187 : RowSquare [4,2,1,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg1033

lemma sg1188 : RowSquare [4,2,1,1,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg178

lemma sg1189 : RowSquare [4,2,1,1,1,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg371

lemma sg1190 : RowSquare [4,2,1,1,1,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg372

lemma sg1191 : RowSquare [4,2,1,1,1,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg373

lemma sg1192 : RowSquare [4,2,1,1,1,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg330

lemma sg1193 : RowSquare [4,2,1,1,1,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg179

lemma sg1194 : RowSquare [4,2,1,1,1,1,1] [4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg179

lemma sg1195 : RowSquare [4,2,2,1,1,1] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg330

lemma sg1196 : RowSquare [4,2,2,1,1,1] [2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg178

lemma sg1197 : RowSquare [4,2,2,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg961

lemma sg1198 : RowSquare [4,2,2,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg178

lemma sg1199 : RowSquare [4,2,2,1,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg180

lemma sg1200 : RowSquare [4,2,2,1,1,1] [3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg181

lemma sg1201 : RowSquare [4,2,2,1,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg143

lemma sg1202 : RowSquare [4,3,1,1,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg940

lemma sg1203 : RowSquare [4,3,1,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg178

lemma sg1204 : RowSquare [4,3,1,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg942

lemma sg1205 : RowSquare [4,3,1,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg762

lemma sg1206 : RowSquare [4,3,1,1,1,1] [3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg178

lemma sg1207 : RowSquare [4,3,1,1,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg67

lemma sg1208 : RowSquare [4,3,1,1,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg68

lemma sg1209 : RowSquare [4,3,1,1,1,1] [4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg548

lemma sg1210 : RowSquare [4,3,1,1,1,1] [4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg11 sg178

lemma sg1211 : RowSquare [4,3,1,1,1,1] [4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg763

lemma sg1212 : RowSquare [4,3,1,1,1,1] [4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg767

lemma sg1213 : RowSquare [4,3,1,1,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg768

lemma sg1214 : RowSquare [4,3,1,1,1,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg34 sg67

lemma sg1215 : RowSquare [4,3,1,1,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg34 sg68

lemma sg1216 : RowSquare [4,3,1,1,1,1] [5,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg456

lemma sg1217 : RowSquare [4,3,1,1,1,1] [5,3,3] := by
  exact rowSquare_join (by decide) sg4 sg239

lemma sg1218 : RowSquare [4,3,1,1,1,1] [5,5,1] := by
  exact rowSquare_join (by decide) sg4 sg241

lemma sg1219 : RowSquare [4,3,1,1,1,1] [6,5] := by
  exact rowSquare_join (by decide) sg5 sg241

lemma sg1220 : RowSquare [4,3,1,1,1,1] [7,2,2] := by
  exact rowSquare_join (by decide) sg4 sg245

lemma sg1221 : RowSquare [4,3,1,1,1,1] [9,2] := by
  exact rowSquare_join (by decide) sg42 sg50

lemma sg1222 : RowSquare [4,3,1,1,1,1] [10,1] := by
  exact rowSquare_join (by decide) sg43 sg50

lemma sg1223 : RowSquare [4,3,2,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg849

lemma sg1224 : RowSquare [4,3,2,1,1] [3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg851

lemma sg1225 : RowSquare [4,3,2,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg792

lemma sg1226 : RowSquare [4,3,2,1,1] [3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg285

lemma sg1227 : RowSquare [4,3,2,1,1] [3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg32 sg55

lemma sg1228 : RowSquare [4,3,2,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg249

lemma sg1229 : RowSquare [4,3,2,1,1] [4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg143

lemma sg1230 : RowSquare [4,3,2,1,1] [4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg251

lemma sg1231 : RowSquare [4,3,2,1,1] [5,3,3] := by
  exact rowSquare_join (by decide) sg9 sg114

lemma sg1233 : RowSquare [4,3,3,1] [2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg65

lemma sg1234 : RowSquare [4,3,3,1] [2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg10 sg128

lemma sg1235 : RowSquare [4,4,1,1,1] [3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg832

lemma sg1236 : RowSquare [4,4,1,1,1] [3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg833

lemma sg1237 : RowSquare [4,4,1,1,1] [3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg834

lemma sg1238 : RowSquare [4,4,2,1] [4,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg125

lemma sg1239 : RowSquare [4,4,3] [3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg516

end UniversalTensorSquare
end
end

end OAI
