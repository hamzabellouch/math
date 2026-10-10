import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes6

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3708 : RowSquare [9,2,2,2] [4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg181 sg371

lemma sg3709 : RowSquare [9,2,2,2] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg180 sg372

lemma sg3710 : RowSquare [9,2,2,2] [4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg180 sg373

lemma sg3711 : RowSquare [9,2,2,2] [4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg181 sg372

lemma sg3712 : RowSquare [9,2,2,2] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg181 sg373

lemma sg3713 : RowSquare [9,2,2,2] [5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg374

lemma sg3714 : RowSquare [9,2,2,2] [5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg375

lemma sg3715 : RowSquare [9,2,2,2] [5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg376

lemma sg3716 : RowSquare [9,2,2,2] [5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg182 sg373

lemma sg3717 : RowSquare [9,2,2,2] [5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg377

lemma sg3718 : RowSquare [9,2,2,2] [5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg378

lemma sg3719 : RowSquare [9,2,2,2] [5,4,3,3] := by
  exact rowSquare_join (by decide) sg183 sg373

lemma sg3720 : RowSquare [9,2,2,2] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg383

lemma sg3721 : RowSquare [9,3,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg586

lemma sg3722 : RowSquare [9,3,1,1,1] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg40 sg1001

lemma sg3723 : RowSquare [9,3,2,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg389

lemma sg3724 : RowSquare [9,3,2,1] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg390

lemma sg3725 : RowSquare [9,3,2,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg1032

lemma sg3726 : RowSquare [9,3,2,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1033

lemma sg3727 : RowSquare [9,3,2,1] [4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg218 sg330

lemma sg3728 : RowSquare [9,3,2,1] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg193 sg371

lemma sg3729 : RowSquare [9,3,2,1] [4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg193 sg373

lemma sg3730 : RowSquare [9,3,2,1] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg194 sg371

lemma sg3731 : RowSquare [9,3,2,1] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg195 sg373

lemma sg3732 : RowSquare [9,3,3] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1061

lemma sg3733 : RowSquare [9,3,3] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg1063

lemma sg3734 : RowSquare [9,3,3] [4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg88 sg636

lemma sg3735 : RowSquare [9,3,3] [4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg88 sg637

lemma sg3736 : RowSquare [9,3,3] [5,5,5] := by
  exact rowSquare_join (by decide) sg89 sg641

lemma sg3737 : RowSquare [9,4,1,1] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg40 sg1033

lemma sg3738 : RowSquare [9,4,1,1] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg407

lemma sg3741 : RowSquare [2,2,2,2,2,2,2,1,1] [6,6,2,2] := by
  exact rowSquare_join (by decide) sg364 sg407

lemma sg3744 : RowSquare [3,2,2,2,2,2,2,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg364 sg358

lemma sg3745 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [8,2,2,2,2] := by
  exact rowSquare_join (by decide) sg413 sg413

lemma sg3746 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [8,3,2,2,1] := by
  exact rowSquare_join (by decide) sg413 sg414

lemma sg3747 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [8,3,3,1,1] := by
  exact rowSquare_join (by decide) sg413 sg415

lemma sg3748 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [8,4,2,2] := by
  exact rowSquare_join (by decide) sg414 sg414

lemma sg3749 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [8,4,3,1] := by
  exact rowSquare_join (by decide) sg414 sg415

lemma sg3750 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [9,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg234 sg636

lemma sg3751 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [9,3,2,2] := by
  exact rowSquare_join (by decide) sg414 sg416

lemma sg3752 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [9,5,1,1] := by
  exact rowSquare_join (by decide) sg414 sg418

lemma sg3753 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [10,4,1,1] := by
  exact rowSquare_join (by decide) sg414 sg420

lemma sg3754 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [10,5,1] := by
  exact rowSquare_join (by decide) sg417 sg418

lemma sg3755 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [11,3,1,1] := by
  exact rowSquare_join (by decide) sg352 sg426

lemma sg3756 : RowSquare [3,3,1,1,1,1,1,1,1,1,1,1] [12,2,1,1] := by
  exact rowSquare_join (by decide) sg414 sg421

lemma sg3757 : RowSquare [3,3,2,1,1,1,1,1,1,1,1] [6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg389 sg413

lemma sg3758 : RowSquare [3,3,2,1,1,1,1,1,1,1,1] [6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg413 sg390

lemma sg3759 : RowSquare [3,3,2,1,1,1,1,1,1,1,1] [6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg218 sg694

lemma sg3760 : RowSquare [3,3,2,1,1,1,1,1,1,1,1] [6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg389 sg414

lemma sg3761 : RowSquare [3,3,2,1,1,1,1,1,1,1,1] [6,4,3,3] := by
  exact rowSquare_join (by decide) sg390 sg414

lemma sg3762 : RowSquare [3,3,2,1,1,1,1,1,1,1,1] [6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg389 sg415

lemma sg3763 : RowSquare [3,3,2,1,1,1,1,1,1,1,1] [6,4,4,2] := by
  exact rowSquare_join (by decide) sg390 sg415

lemma sg3764 : RowSquare [3,3,2,1,1,1,1,1,1,1,1] [6,5,5] := by
  exact rowSquare_join (by decide) sg220 sg696

lemma sg3765 : RowSquare [3,3,2,1,1,1,1,1,1,1,1] [6,6,4] := by
  exact rowSquare_join (by decide) sg89 sg1110

lemma sg3766 : RowSquare [3,3,2,2,1,1,1,1,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg389 sg389

lemma sg3767 : RowSquare [3,3,2,2,1,1,1,1,1,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg389 sg390

lemma sg3768 : RowSquare [3,3,2,2,1,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg390

lemma sg3769 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg218 sg644

lemma sg3770 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg694

lemma sg3771 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg193 sg695

lemma sg3772 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg389 sg392

lemma sg3773 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg392 sg390

lemma sg3774 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg696

lemma sg3775 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg389 sg393

lemma sg3776 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,4,4,3] := by
  exact rowSquare_join (by decide) sg390 sg393

lemma sg3777 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg1109

lemma sg3778 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg694

lemma sg3779 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg228 sg636

lemma sg3780 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg389 sg394

lemma sg3781 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg390 sg394

lemma sg3782 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg389 sg395

lemma sg3783 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,5,4,2] := by
  exact rowSquare_join (by decide) sg390 sg395

lemma sg3784 : RowSquare [3,3,2,2,1,1,1,1,1,1] [5,5,5,1] := by
  exact rowSquare_join (by decide) sg195 sg696

lemma sg3785 : RowSquare [3,3,2,2,1,1,1,1,1,1] [6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg391 sg391

lemma sg3786 : RowSquare [3,3,2,2,1,1,1,1,1,1] [6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg348 sg424

lemma sg3787 : RowSquare [3,3,2,2,1,1,1,1,1,1] [6,6,2,2] := by
  exact rowSquare_join (by decide) sg390 sg396

lemma sg3788 : RowSquare [3,3,2,2,2,2,1,1] [4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg403

lemma sg3789 : RowSquare [3,3,2,2,2,2,2] [8,8] := by
  exact rowSquare_join (by decide) sg367 sg311

lemma sg3790 : RowSquare [3,3,3,2,1,1,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg1063

lemma sg3791 : RowSquare [3,3,3,2,1,1,1,1,1] [4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg975

lemma sg3792 : RowSquare [3,3,3,2,1,1,1,1,1] [4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg348 sg389

lemma sg3793 : RowSquare [3,3,3,2,1,1,1,1,1] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg348 sg390

lemma sg3794 : RowSquare [3,3,3,2,1,1,1,1,1] [4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg194 sg637

lemma sg3795 : RowSquare [3,3,3,2,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg350

lemma sg3796 : RowSquare [3,3,3,2,1,1,1,1,1] [5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg415

lemma sg3797 : RowSquare [4,2,2,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg422

lemma sg3798 : RowSquare [4,2,2,2,2,2,1,1] [4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg561

lemma sg3799 : RowSquare [4,2,2,2,2,2,1,1] [4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg365

lemma sg3800 : RowSquare [4,2,2,2,2,2,1,1] [4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg958

lemma sg3801 : RowSquare [4,2,2,2,2,2,1,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg333 sg364

lemma sg3802 : RowSquare [4,2,2,2,2,2,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg364 sg334

lemma sg3803 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg413

lemma sg3804 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg414

lemma sg3805 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg413

lemma sg3806 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg415

lemma sg3807 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg372 sg413

lemma sg3808 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg413 sg373

lemma sg3809 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg415

lemma sg3810 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,4,3,3] := by
  exact rowSquare_join (by decide) sg373 sg414

lemma sg3811 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg372 sg415

lemma sg3812 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [6,4,4,2] := by
  exact rowSquare_join (by decide) sg373 sg415

lemma sg3813 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg416

lemma sg3814 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg374 sg413

lemma sg3815 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg417

lemma sg3816 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg416

lemma sg3817 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,3,2,2,2] := by
  exact rowSquare_join (by decide) sg375 sg413

lemma sg3818 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg374 sg415

lemma sg3819 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,3,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg416

lemma sg3820 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,3,3,3] := by
  exact rowSquare_join (by decide) sg373 sg416

lemma sg3821 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg418

lemma sg3822 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg417

lemma sg3823 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,4,2,2,1] := by
  exact rowSquare_join (by decide) sg375 sg414

lemma sg3824 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,4,3,1,1] := by
  exact rowSquare_join (by decide) sg372 sg417

lemma sg3825 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,4,3,2] := by
  exact rowSquare_join (by decide) sg373 sg417

lemma sg3826 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,4,4,1] := by
  exact rowSquare_join (by decide) sg376 sg415

lemma sg3827 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg418

lemma sg3828 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,5,2,1,1] := by
  exact rowSquare_join (by decide) sg372 sg418

lemma sg3829 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,5,2,2] := by
  exact rowSquare_join (by decide) sg373 sg418

lemma sg3830 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,5,3,1] := by
  exact rowSquare_join (by decide) sg377 sg415

lemma sg3831 : RowSquare [4,3,1,1,1,1,1,1,1,1,1] [7,5,4] := by
  exact rowSquare_join (by decide) sg378 sg415

lemma sg3832 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg389

lemma sg3833 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg390

lemma sg3834 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg87 sg1032

lemma sg3835 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg87 sg1033

lemma sg3836 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg694

lemma sg3837 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg695

lemma sg3838 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg696

lemma sg3839 : RowSquare [4,3,2,1,1,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg390 sg373

lemma sg3840 : RowSquare [4,3,2,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg413

lemma sg3841 : RowSquare [4,3,2,1,1,1,1,1,1,1] [5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg414

lemma sg3842 : RowSquare [4,3,2,1,1,1,1,1,1,1] [5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg391

lemma sg3843 : RowSquare [4,3,2,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg415

lemma sg3844 : RowSquare [4,3,2,1,1,1,1,1,1,1] [5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg391 sg373

lemma sg3845 : RowSquare [4,3,2,1,1,1,1,1,1,1] [5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg218 sg616

lemma sg3846 : RowSquare [4,3,2,1,1,1,1,1,1,1] [5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg392

lemma sg3847 : RowSquare [4,3,2,1,1,1,1,1,1,1] [5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg701

lemma sg3848 : RowSquare [4,3,2,1,1,1,1,1,1,1] [5,5,5,1] := by
  exact rowSquare_join (by decide) sg181 sg696

lemma sg3849 : RowSquare [4,3,2,2,1,1,1,1,1] [4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg391

lemma sg3850 : RowSquare [4,3,2,2,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg849

lemma sg3851 : RowSquare [4,3,2,2,1,1,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg359

lemma sg3852 : RowSquare [4,3,2,2,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg106 sg849

lemma sg3853 : RowSquare [4,3,2,2,1,1,1,1,1] [6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg850

lemma sg3854 : RowSquare [4,3,2,2,1,1,1,1,1] [6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg3181

lemma sg3855 : RowSquare [4,3,2,2,1,1,1,1,1] [6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg850

lemma sg3856 : RowSquare [4,3,2,2,1,1,1,1,1] [6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg3182

lemma sg3857 : RowSquare [4,3,2,2,1,1,1,1,1] [6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg399

lemma sg3858 : RowSquare [4,3,2,2,2,2,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg879

lemma sg3859 : RowSquare [4,3,2,2,2,2,1] [4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg849

lemma sg3860 : RowSquare [4,3,2,2,2,2,1] [4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg165 sg561

lemma sg3861 : RowSquare [4,3,2,2,2,2,1] [4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg850

lemma sg3862 : RowSquare [4,3,2,2,2,2,1] [5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg850

lemma sg3863 : RowSquare [4,3,2,2,2,2,1] [5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg85 sg849

lemma sg3864 : RowSquare [4,3,2,2,2,2,1] [7,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg86 sg849

lemma sg3865 : RowSquare [4,3,3,2,1,1,1,1] [7,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg96 sg849

lemma sg3866 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg370

lemma sg3867 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg371

lemma sg3868 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg372

lemma sg3869 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg373

lemma sg3870 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg371

lemma sg3871 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg372

lemma sg3872 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg371 sg373

lemma sg3873 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg372 sg372

lemma sg3874 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg372 sg373

lemma sg3875 : RowSquare [4,4,1,1,1,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg373

lemma sg3876 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg374

lemma sg3877 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg375

lemma sg3878 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg374

lemma sg3879 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg376

lemma sg3880 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg374 sg372

lemma sg3881 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg374 sg373

lemma sg3882 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg377

lemma sg3883 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg375

lemma sg3884 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg378

lemma sg3885 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg376

lemma sg3886 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg372 sg375

lemma sg3887 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg375 sg373

lemma sg3888 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg372 sg376

lemma sg3889 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,4,4,3] := by
  exact rowSquare_join (by decide) sg373 sg376

lemma sg3890 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg377

lemma sg3891 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg378

lemma sg3892 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg377

lemma sg3893 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg373 sg377

lemma sg3894 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg372 sg378

lemma sg3895 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,5,4,2] := by
  exact rowSquare_join (by decide) sg373 sg378

lemma sg3896 : RowSquare [4,4,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg370 sg379

lemma sg3897 : RowSquare [4,4,1,1,1,1,1,1,1,1] [6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg374 sg374

lemma sg3898 : RowSquare [4,4,1,1,1,1,1,1,1,1] [6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg371 sg379

lemma sg3899 : RowSquare [4,4,1,1,1,1,1,1,1,1] [6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg372 sg379

lemma sg3900 : RowSquare [4,4,1,1,1,1,1,1,1,1] [6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg379 sg373

lemma sg3901 : RowSquare [4,4,1,1,1,1,1,1,1,1] [6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg375 sg375

lemma sg3902 : RowSquare [4,4,1,1,1,1,1,1,1,1] [6,5,3,2] := by
  exact rowSquare_join (by decide) sg373 sg382

lemma sg3903 : RowSquare [4,4,1,1,1,1,1,1,1,1] [6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg383

lemma sg3904 : RowSquare [4,4,1,1,1,1,1,1,1,1] [7,6,1,1,1] := by
  exact rowSquare_join (by decide) sg375 sg383

lemma sg3905 : RowSquare [4,4,1,1,1,1,1,1,1,1] [8,8] := by
  exact rowSquare_join (by decide) sg383 sg383

lemma sg3906 : RowSquare [4,4,1,1,1,1,1,1,1,1] [9,7] := by
  exact rowSquare_join (by decide) sg383 sg386

lemma sg3907 : RowSquare [4,4,1,1,1,1,1,1,1,1] [10,6] := by
  exact rowSquare_join (by decide) sg14 sg1577

lemma sg3908 : RowSquare [4,4,1,1,1,1,1,1,1,1] [11,5] := by
  exact rowSquare_join (by decide) sg14 sg1578

lemma sg3909 : RowSquare [4,4,1,1,1,1,1,1,1,1] [12,4] := by
  exact rowSquare_join (by decide) sg14 sg1579

lemma sg3910 : RowSquare [4,4,1,1,1,1,1,1,1,1] [13,3] := by
  exact rowSquare_join (by decide) sg14 sg1580

lemma sg3911 : RowSquare [4,4,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg370

lemma sg3912 : RowSquare [4,4,2,1,1,1,1,1,1] [3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg371

lemma sg3913 : RowSquare [4,4,2,1,1,1,1,1,1] [3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg372

lemma sg3914 : RowSquare [4,4,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg373

lemma sg3915 : RowSquare [4,4,2,1,1,1,1,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg370 sg331

lemma sg3916 : RowSquare [4,4,2,1,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg334

lemma sg3917 : RowSquare [4,4,2,1,1,1,1,1,1] [6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg342

lemma sg3918 : RowSquare [4,4,2,1,1,1,1,1,1] [7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg387

lemma sg3919 : RowSquare [4,4,2,1,1,1,1,1,1] [7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg343

lemma sg3920 : RowSquare [4,4,2,1,1,1,1,1,1] [7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg388

lemma sg3921 : RowSquare [4,4,2,1,1,1,1,1,1] [7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg344

lemma sg3922 : RowSquare [4,4,2,1,1,1,1,1,1] [7,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2500

lemma sg3923 : RowSquare [4,4,2,1,1,1,1,1,1] [7,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2501

lemma sg3924 : RowSquare [4,4,2,1,1,1,1,1,1] [7,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg2502

lemma sg3925 : RowSquare [4,4,2,1,1,1,1,1,1] [7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg345

lemma sg3926 : RowSquare [4,4,2,1,1,1,1,1,1] [7,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2503

lemma sg3927 : RowSquare [4,4,2,1,1,1,1,1,1] [8,8] := by
  exact rowSquare_join (by decide) sg14 sg1581

lemma sg3928 : RowSquare [4,4,2,1,1,1,1,1,1] [9,7] := by
  exact rowSquare_join (by decide) sg14 sg1582

lemma sg3929 : RowSquare [4,4,2,1,1,1,1,1,1] [10,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg1123

lemma sg3930 : RowSquare [4,4,2,1,1,1,1,1,1] [10,6] := by
  exact rowSquare_join (by decide) sg29 sg1122

lemma sg3931 : RowSquare [4,4,2,1,1,1,1,1,1] [11,5] := by
  exact rowSquare_join (by decide) sg29 sg1124

lemma sg3932 : RowSquare [4,4,2,1,1,1,1,1,1] [12,4] := by
  exact rowSquare_join (by decide) sg29 sg1125

lemma sg3933 : RowSquare [4,4,2,1,1,1,1,1,1] [13,3] := by
  exact rowSquare_join (by decide) sg174 sg427

lemma sg3934 : RowSquare [4,4,2,1,1,1,1,1,1] [14,2] := by
  exact rowSquare_join (by decide) sg176 sg427

lemma sg3935 : RowSquare [4,4,2,2,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg1650

lemma sg3936 : RowSquare [4,4,2,2,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg1651

lemma sg3937 : RowSquare [4,4,2,2,2,1,1] [4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg1650

lemma sg3938 : RowSquare [4,4,2,2,2,1,1] [4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1651

lemma sg3939 : RowSquare [4,4,2,2,2,1,1] [4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1651

lemma sg3940 : RowSquare [4,4,2,2,2,1,1] [4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1652

lemma sg3941 : RowSquare [4,4,2,2,2,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg332 sg295

lemma sg3942 : RowSquare [4,4,2,2,2,1,1] [5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg1650

lemma sg3943 : RowSquare [4,4,2,2,2,1,1] [5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg1651

lemma sg3944 : RowSquare [4,4,2,2,2,1,1] [6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg1651

lemma sg3945 : RowSquare [5,3,1,1,1,1,1,1,1,1] [6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg224 sg586

lemma sg3946 : RowSquare [5,3,1,1,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg225 sg586

lemma sg3947 : RowSquare [5,3,1,1,1,1,1,1,1,1] [6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg223 sg587

lemma sg3948 : RowSquare [5,3,2,1,1,1,1,1,1] [3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg194 sg586

lemma sg3949 : RowSquare [5,3,2,1,1,1,1,1,1] [3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg998

lemma sg3950 : RowSquare [5,3,2,1,1,1,1,1,1] [3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg910

lemma sg3951 : RowSquare [5,3,2,1,1,1,1,1,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg999

lemma sg3952 : RowSquare [5,3,2,1,1,1,1,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg1000

lemma sg3953 : RowSquare [5,3,2,1,1,1,1,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg1001

lemma sg3954 : RowSquare [5,3,2,1,1,1,1,1,1] [4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg90 sg910

lemma sg3955 : RowSquare [5,3,2,1,1,1,1,1,1] [4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg910

lemma sg3956 : RowSquare [5,3,2,1,1,1,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg1006

lemma sg3957 : RowSquare [5,3,2,1,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg1682

lemma sg3958 : RowSquare [5,3,2,1,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg94 sg910

lemma sg3959 : RowSquare [5,3,2,2,2,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg358 sg271

lemma sg3960 : RowSquare [5,3,2,2,2,1,1] [5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg1682

lemma sg3961 : RowSquare [5,3,2,2,2,1,1] [5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1689

lemma sg3962 : RowSquare [5,3,2,2,2,1,1] [6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg1683

lemma sg3963 : RowSquare [5,3,3,2,2,1] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg306 sg271

lemma sg3964 : RowSquare [5,4,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg586

lemma sg3965 : RowSquare [5,4,1,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg586

lemma sg3966 : RowSquare [5,4,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg587

lemma sg3967 : RowSquare [5,4,1,1,1,1,1,1,1] [3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg588

lemma sg3968 : RowSquare [5,4,1,1,1,1,1,1,1] [4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg589

lemma sg3969 : RowSquare [5,4,1,1,1,1,1,1,1] [7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg191 sg586

lemma sg3970 : RowSquare [5,4,1,1,1,1,1,1,1] [7,7,1,1] := by
  exact rowSquare_join (by decide) sg377 sg324

lemma sg3971 : RowSquare [5,4,1,1,1,1,1,1,1] [7,7,2] := by
  exact rowSquare_join (by decide) sg378 sg324

lemma sg3972 : RowSquare [5,4,1,1,1,1,1,1,1] [8,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg192 sg586

lemma sg3973 : RowSquare [5,4,1,1,1,1,1,1,1] [8,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2521

lemma sg3974 : RowSquare [5,4,1,1,1,1,1,1,1] [8,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2522

lemma sg3975 : RowSquare [5,4,1,1,1,1,1,1,1] [8,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1584

lemma sg3976 : RowSquare [5,4,1,1,1,1,1,1,1] [8,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg2021

lemma sg3977 : RowSquare [5,4,1,1,1,1,1,1,1] [8,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2523

lemma sg3978 : RowSquare [5,4,1,1,1,1,1,1,1] [8,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2026

lemma sg3979 : RowSquare [5,4,1,1,1,1,1,1,1] [8,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg1585

lemma sg3980 : RowSquare [5,4,1,1,1,1,1,1,1] [8,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2027

lemma sg3981 : RowSquare [5,4,1,1,1,1,1,1,1] [8,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2025

lemma sg3982 : RowSquare [5,4,1,1,1,1,1,1,1] [8,8] := by
  exact rowSquare_join (by decide) sg383 sg324

lemma sg3983 : RowSquare [5,4,2,1,1,1,1,1] [3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg910

lemma sg3984 : RowSquare [5,4,2,1,1,1,1,1] [3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg910

lemma sg3985 : RowSquare [5,4,2,1,1,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg66 sg915

lemma sg3986 : RowSquare [5,4,2,1,1,1,1,1] [4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg910

lemma sg3987 : RowSquare [5,4,2,1,1,1,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg373 sg271

lemma sg3988 : RowSquare [5,4,2,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2534

lemma sg3989 : RowSquare [5,4,2,2,2,1] [5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2605

lemma sg3990 : RowSquare [5,4,2,2,2,1] [5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg2606

lemma sg3991 : RowSquare [5,4,2,2,2,1] [5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2609

lemma sg3992 : RowSquare [5,4,3,2,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg759

lemma sg3993 : RowSquare [5,4,3,2,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg3249

lemma sg3994 : RowSquare [5,5,1,1,1,1,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg2546

lemma sg3995 : RowSquare [5,5,1,1,1,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg313 sg313

lemma sg3996 : RowSquare [5,5,1,1,1,1,1,1] [5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg1592

lemma sg3997 : RowSquare [5,5,1,1,1,1,1,1] [6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg2553

lemma sg3999 : RowSquare [5,5,2,2,2] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg121 sg509

lemma sg4000 : RowSquare [5,5,2,2,2] [2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg120 sg509

lemma sg4001 : RowSquare [5,5,2,2,2] [2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg118 sg509

lemma sg4002 : RowSquare [5,5,2,2,2] [2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg118 sg507

lemma sg4003 : RowSquare [5,5,2,2,2] [2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg118 sg506

lemma sg4004 : RowSquare [5,5,2,2,2] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg118 sg503

lemma sg4005 : RowSquare [5,5,2,2,2] [2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg1617

lemma sg4006 : RowSquare [5,5,2,2,2] [3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg119 sg509

lemma sg4007 : RowSquare [5,5,2,2,2] [3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg117 sg509

lemma sg4008 : RowSquare [5,5,2,2,2] [3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg115 sg508

lemma sg4009 : RowSquare [5,5,2,2,2] [3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg115 sg507

lemma sg4010 : RowSquare [5,5,2,2,2] [3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg115 sg506

lemma sg4011 : RowSquare [5,5,2,2,2] [3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg115 sg503

lemma sg4012 : RowSquare [5,5,2,2,2] [3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg114 sg509

lemma sg4013 : RowSquare [5,5,2,2,2] [3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg114 sg508

lemma sg4014 : RowSquare [5,5,2,2,2] [3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg114 sg507

lemma sg4015 : RowSquare [5,5,2,2,2] [3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg114 sg506

lemma sg4016 : RowSquare [5,5,2,2,2] [3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg115 sg500

lemma sg4017 : RowSquare [5,5,2,2,2] [3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg114 sg505

lemma sg4018 : RowSquare [5,5,2,2,2] [4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg116 sg509

lemma sg4019 : RowSquare [5,5,2,2,2] [4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg116 sg503

lemma sg4020 : RowSquare [5,5,2,2,2] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg1617

lemma sg4021 : RowSquare [5,5,2,2,2] [4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg116 sg504

lemma sg4022 : RowSquare [5,5,2,2,2] [5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg120 sg501

lemma sg4023 : RowSquare [6,3,1,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg1327

lemma sg4024 : RowSquare [6,3,2,1,1,1,1,1] [3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg889

lemma sg4025 : RowSquare [6,3,2,1,1,1,1,1] [3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg890

lemma sg4026 : RowSquare [6,3,2,1,1,1,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg891

lemma sg4027 : RowSquare [6,3,2,1,1,1,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg892

lemma sg4028 : RowSquare [6,3,2,1,1,1,1,1] [4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg3263

lemma sg4029 : RowSquare [6,3,2,1,1,1,1,1] [4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg3264

lemma sg4030 : RowSquare [6,3,2,1,1,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg897

lemma sg4031 : RowSquare [6,3,2,2,2,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg762

lemma sg4032 : RowSquare [6,3,2,2,2,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg765

lemma sg4033 : RowSquare [6,3,2,2,2,1] [4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg76 sg762

lemma sg4034 : RowSquare [6,3,3,2,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg1178

lemma sg4035 : RowSquare [6,3,3,2,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg752

lemma sg4036 : RowSquare [6,3,3,2,1,1] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg754

lemma sg4037 : RowSquare [6,3,3,2,1,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg440

lemma sg4038 : RowSquare [6,3,3,2,1,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg32 sg1144

lemma sg4039 : RowSquare [6,3,3,2,1,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg32 sg1145

lemma sg4040 : RowSquare [6,3,3,3,1] [4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg313 sg254

lemma sg4041 : RowSquare [6,3,3,3,1] [4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg67 sg759

lemma sg4042 : RowSquare [6,3,3,3,1] [4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg446

lemma sg4043 : RowSquare [6,3,3,3,1] [4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg68 sg759

lemma sg4044 : RowSquare [6,3,3,3,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg314 sg254

lemma sg4045 : RowSquare [6,3,3,3,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg254 sg315

lemma sg4046 : RowSquare [6,3,3,3,1] [5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg313 sg255

lemma sg4047 : RowSquare [6,3,3,3,1] [5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg71 sg759

lemma sg4048 : RowSquare [6,3,3,3,1] [5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg314 sg255

lemma sg4049 : RowSquare [6,3,3,3,1] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg254 sg319

lemma sg4050 : RowSquare [6,4,1,1,1,1,1,1] [4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg22 sg1327

lemma sg4051 : RowSquare [6,4,1,1,1,1,1,1] [4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg2546

lemma sg4052 : RowSquare [6,4,1,1,1,1,1,1] [4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg1327

lemma sg4053 : RowSquare [6,4,1,1,1,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg66 sg892

lemma sg4054 : RowSquare [6,4,1,1,1,1,1,1] [5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg1327

lemma sg4055 : RowSquare [6,4,1,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg22 sg1328

lemma sg4056 : RowSquare [6,4,1,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg1328

lemma sg4057 : RowSquare [6,4,1,1,1,1,1,1] [5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg3284

lemma sg4058 : RowSquare [6,4,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg1327

lemma sg4059 : RowSquare [6,4,1,1,1,1,1,1] [6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg2550

lemma sg4060 : RowSquare [6,4,1,1,1,1,1,1] [8,8] := by
  exact rowSquare_join (by decide) sg17 sg1606

lemma sg4061 : RowSquare [6,4,2,1,1,1,1] [4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2073

lemma sg4062 : RowSquare [6,4,2,1,1,1,1] [4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1146

lemma sg4064 : RowSquare [6,4,2,2,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg347 sg248

lemma sg4065 : RowSquare [6,4,2,2,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg346 sg248

lemma sg4066 : RowSquare [6,4,2,2,1,1] [2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg345 sg248

lemma sg4067 : RowSquare [6,4,2,2,1,1] [2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg247

lemma sg4068 : RowSquare [6,4,2,2,1,1] [2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg246

lemma sg4069 : RowSquare [6,4,2,2,1,1] [2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg342 sg244

lemma sg4070 : RowSquare [6,4,2,2,1,1] [2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg342 sg241

lemma sg4071 : RowSquare [6,4,2,2,1,1] [3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg344 sg248

lemma sg4072 : RowSquare [6,4,2,2,1,1] [3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg341 sg246

lemma sg4073 : RowSquare [6,4,2,2,1,1] [3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg340 sg248

lemma sg4074 : RowSquare [6,4,2,2,1,1] [3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg339 sg248

lemma sg4075 : RowSquare [6,4,2,2,1,1] [3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg339 sg246

lemma sg4076 : RowSquare [6,4,2,2,1,1] [3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg339 sg241

lemma sg4077 : RowSquare [6,4,2,2,1,1] [3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1628

lemma sg4078 : RowSquare [6,4,2,2,1,1] [3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg339 sg239

lemma sg4079 : RowSquare [6,4,2,2,1,1] [3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg148 sg459

lemma sg4080 : RowSquare [6,4,2,2,1,1] [4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg337 sg248

lemma sg4081 : RowSquare [6,4,2,2,1,1] [4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg334 sg248

lemma sg4082 : RowSquare [6,4,2,2,1,1] [4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg1630

lemma sg4083 : RowSquare [6,4,2,2,1,1] [4,4,4,4] := by
  exact rowSquare_join (by decide) sg13 sg1631

lemma sg4084 : RowSquare [6,4,2,2,1,1] [5,5,3,3] := by
  exact rowSquare_join (by decide) sg67 sg767

lemma sg4085 : RowSquare [6,4,2,2,1,1] [5,5,4,2] := by
  exact rowSquare_join (by decide) sg144 sg458

lemma sg4086 : RowSquare [6,4,2,2,1,1] [6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2574

lemma sg4087 : RowSquare [6,4,2,2,1,1] [6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2079

lemma sg4088 : RowSquare [6,4,2,2,1,1] [6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg2081

lemma sg4089 : RowSquare [6,4,2,2,1,1] [6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg242

lemma sg4090 : RowSquare [6,4,2,2,1,1] [6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2591

lemma sg4091 : RowSquare [6,4,2,2,1,1] [6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg142 sg460

lemma sg4092 : RowSquare [6,4,2,2,1,1] [6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2080

lemma sg4093 : RowSquare [6,4,2,2,1,1] [6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg243

lemma sg4094 : RowSquare [6,4,2,2,1,1] [6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg56 sg811

lemma sg4095 : RowSquare [6,4,2,2,1,1] [6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg295 sg260

lemma sg4096 : RowSquare [6,4,2,2,1,1] [6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg239

lemma sg4097 : RowSquare [6,4,2,2,1,1] [6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg142 sg462

lemma sg4098 : RowSquare [6,4,2,2,1,1] [6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg244

lemma sg4099 : RowSquare [6,4,2,2,1,1] [6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg240

lemma sg4100 : RowSquare [6,4,2,2,1,1] [6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg295 sg261

lemma sg4101 : RowSquare [6,4,2,2,1,1] [6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg241

lemma sg4102 : RowSquare [6,4,2,2,1,1] [6,6,2,2] := by
  exact rowSquare_join (by decide) sg334 sg241

lemma sg4103 : RowSquare [6,4,2,2,1,1] [7,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg2079

lemma sg4104 : RowSquare [6,4,2,2,1,1] [7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg2081

lemma sg4105 : RowSquare [6,4,2,2,1,1] [7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg245

lemma sg4106 : RowSquare [6,4,2,2,1,1] [7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg242

lemma sg4107 : RowSquare [6,4,2,2,1,1] [7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg246

lemma sg4108 : RowSquare [6,4,2,2,1,1] [7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg243

lemma sg4109 : RowSquare [6,4,2,2,1,1] [8,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8 sg1678

lemma sg4110 : RowSquare [6,4,2,2,1,1] [8,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg247

lemma sg4111 : RowSquare [6,4,3,1,1,1] [3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg32 sg1178

lemma sg4112 : RowSquare [6,4,3,1,1,1] [4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg752

lemma sg4113 : RowSquare [6,4,3,1,1,1] [4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg1195

end UniversalTensorSquare
end
end

end OAI
