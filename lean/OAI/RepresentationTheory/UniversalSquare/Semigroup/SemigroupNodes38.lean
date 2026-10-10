import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37

namespace OAI

/-! Semigroup Nodes 38. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15740 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15297

lemma sg15741 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3636 sg4217

lemma sg15742 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4243

lemma sg15743 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4128

lemma sg15744 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg3360 sg4446

lemma sg15745 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4244

lemma sg15746 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4129

lemma sg15747 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15298

lemma sg15748 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,3] := by
  exact rowSquare_join (by decide) sg3360 sg4447

lemma sg15749 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,2] := by
  exact rowSquare_join (by decide) sg3360 sg4448

lemma sg15750 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4130

lemma sg15751 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15299

lemma sg15752 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15300

lemma sg15753 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15301

lemma sg15754 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg0 sg15302

lemma sg15755 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg0 sg15303

lemma sg15756 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg0 sg15304

lemma sg15757 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg3568 sg4325

lemma sg15758 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3568 sg4326

lemma sg15759 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2917 sg4886

lemma sg15760 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3686 sg4126

lemma sg15761 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4219

lemma sg15762 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,4] := by
  exact rowSquare_join (by decide) sg3360 sg4449

lemma sg15763 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4127

lemma sg15764 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,3] := by
  exact rowSquare_join (by decide) sg3419 sg4400

lemma sg15765 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg3707 sg4120

lemma sg15766 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg4221

lemma sg15767 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg3360 sg4450

lemma sg15768 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg3360 sg4451

lemma sg15769 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg3420 sg4401

lemma sg15770 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4130

lemma sg15771 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4226

lemma sg15772 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg3725 sg4040

lemma sg15773 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,4,1] := by
  exact rowSquare_join (by decide) sg3725 sg4041

lemma sg15774 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg3726 sg4041

lemma sg15775 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4246

lemma sg15776 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3688 sg4128

lemma sg15777 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3432 sg4398

lemma sg15778 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3723 sg4042

lemma sg15779 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3688 sg4129

lemma sg15780 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg4223

lemma sg15781 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg3724 sg4042

lemma sg15782 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg4224

lemma sg15783 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg3360 sg4452

lemma sg15784 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3723 sg4043

lemma sg15785 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg3360 sg4453

lemma sg15786 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3688 sg4130

lemma sg15787 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg4225

lemma sg15788 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,1,1] := by
  exact rowSquare_join (by decide) sg3723 sg4044

lemma sg15789 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,2] := by
  exact rowSquare_join (by decide) sg3360 sg4454

lemma sg15790 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,4,1] := by
  exact rowSquare_join (by decide) sg3725 sg4043

lemma sg15791 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg3726 sg4043

lemma sg15792 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg4226

lemma sg15793 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,1,1] := by
  exact rowSquare_join (by decide) sg3723 sg4045

lemma sg15794 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,2] := by
  exact rowSquare_join (by decide) sg3360 sg4455

lemma sg15795 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,3,1] := by
  exact rowSquare_join (by decide) sg3725 sg4044

lemma sg15796 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,4] := by
  exact rowSquare_join (by decide) sg3726 sg4044

lemma sg15797 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg3724 sg4045

lemma sg15798 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg3725 sg4045

lemma sg15799 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg3726 sg4045

lemma sg15800 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2660 sg4965

lemma sg15801 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2719 sg4926

lemma sg15802 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3251 sg4544

lemma sg15803 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2658 sg4966

lemma sg15804 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3559 sg4336

lemma sg15805 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg3614 sg4247

lemma sg15806 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3685 sg4131

lemma sg15807 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15305

lemma sg15808 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4248

lemma sg15809 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3251 sg4545

lemma sg15810 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2659 sg4966

lemma sg15811 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3559 sg4337

lemma sg15812 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg3251 sg4546

lemma sg15813 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3561 sg4336

lemma sg15814 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3685 sg4132

lemma sg15815 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15306

lemma sg15816 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15307

lemma sg15817 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4249

lemma sg15818 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15308

lemma sg15819 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3363 sg4444

lemma sg15820 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3685 sg4133

lemma sg15821 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15309

lemma sg15822 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3363 sg4445

lemma sg15823 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15310

lemma sg15824 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3251 sg4547

lemma sg15825 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15311

lemma sg15826 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3251 sg4548

lemma sg15827 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15312

lemma sg15828 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3435 sg4399

lemma sg15829 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4250

lemma sg15830 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15313

lemma sg15831 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4134

lemma sg15832 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15314

lemma sg15833 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15315

lemma sg15834 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15316

lemma sg15835 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg0 sg15317

lemma sg15836 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3559 sg4338

lemma sg15837 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg3251 sg4549

lemma sg15838 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3561 sg4337

lemma sg15839 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3559 sg4339

lemma sg15840 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3633 sg4227

lemma sg15841 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3686 sg4132

lemma sg15842 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15318

lemma sg15843 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15319

lemma sg15844 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3251 sg4550

lemma sg15845 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15320

lemma sg15846 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3563 sg4337

lemma sg15847 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3686 sg4133

lemma sg15848 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15321

lemma sg15849 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4251

lemma sg15850 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15322

lemma sg15851 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15323

lemma sg15852 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15324

lemma sg15853 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15325

lemma sg15854 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4135

lemma sg15855 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15326

lemma sg15856 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15327

lemma sg15857 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15328

lemma sg15858 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4136

lemma sg15859 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15329

lemma sg15860 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15330

lemma sg15861 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg0 sg15331

lemma sg15862 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg0 sg15332

lemma sg15863 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3688 sg4133

lemma sg15864 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15333

lemma sg15865 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4252

lemma sg15866 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15334

lemma sg15867 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4253

lemma sg15868 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15335

lemma sg15869 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15336

lemma sg15870 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15337

lemma sg15871 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg0 sg15338

lemma sg15872 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15339

lemma sg15873 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15340

lemma sg15874 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15341

lemma sg15875 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15342

lemma sg15876 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15343

lemma sg15877 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,2] := by
  exact rowSquare_join (by decide) sg0 sg15344

lemma sg15878 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg22 sg12723

lemma sg15879 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15345

lemma sg15880 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15346

lemma sg15881 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,2] := by
  exact rowSquare_join (by decide) sg0 sg15347

lemma sg15882 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg0 sg15348

lemma sg15883 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,5] := by
  exact rowSquare_join (by decide) sg0 sg15349

lemma sg15884 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3561 sg4338

lemma sg15885 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3685 sg4138

lemma sg15886 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3633 sg4228

lemma sg15887 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3563 sg4338

lemma sg15888 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3561 sg4339

lemma sg15889 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3635 sg4227

lemma sg15890 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4254

lemma sg15891 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15350

lemma sg15892 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15351

lemma sg15893 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4255

lemma sg15894 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15352

lemma sg15895 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4139

lemma sg15896 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15353

lemma sg15897 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg3704 sg4123

lemma sg15898 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3563 sg4339

lemma sg15899 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15354

lemma sg15900 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4256

lemma sg15901 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15355

lemma sg15902 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4257

lemma sg15903 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4140

lemma sg15904 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15356

lemma sg15905 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15357

lemma sg15906 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg0 sg15358

lemma sg15907 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4141

lemma sg15908 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15359

lemma sg15909 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15360

lemma sg15910 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15361

lemma sg15911 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg0 sg15362

lemma sg15912 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,5,1] := by
  exact rowSquare_join (by decide) sg23 sg12723

lemma sg15913 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15363

lemma sg15914 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4258

lemma sg15915 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4142

lemma sg15916 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15364

lemma sg15917 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4143

lemma sg15918 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15365

lemma sg15919 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15366

lemma sg15920 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15367

lemma sg15921 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg0 sg15368

lemma sg15922 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4137

lemma sg15923 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15369

lemma sg15924 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,2] := by
  exact rowSquare_join (by decide) sg0 sg15370

lemma sg15925 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,4,1] := by
  exact rowSquare_join (by decide) sg0 sg15371

lemma sg15926 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,5] := by
  exact rowSquare_join (by decide) sg0 sg15372

lemma sg15927 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15373

lemma sg15928 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15374

lemma sg15929 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,3,1] := by
  exact rowSquare_join (by decide) sg0 sg15375

lemma sg15930 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg0 sg15376

lemma sg15931 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3686 sg4138

lemma sg15932 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3635 sg4228

lemma sg15933 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4259

lemma sg15934 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3450 sg4397

lemma sg15935 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3688 sg4138

lemma sg15936 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3636 sg4228

lemma sg15937 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4260

lemma sg15938 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3641 sg4219

lemma sg15939 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4261

lemma sg15940 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4139

lemma sg15941 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4229

lemma sg15942 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4230

lemma sg15943 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3707 sg4123

lemma sg15944 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3641 sg4220

lemma sg15945 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4262

lemma sg15946 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3688 sg4139

lemma sg15947 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4231

lemma sg15948 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4140

lemma sg15949 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg4229

lemma sg15950 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4232

lemma sg15951 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,3] := by
  exact rowSquare_join (by decide) sg3360 sg4458

lemma sg15952 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,4,2] := by
  exact rowSquare_join (by decide) sg3360 sg4459

lemma sg15953 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4141

lemma sg15954 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4233

lemma sg15955 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,3,2] := by
  exact rowSquare_join (by decide) sg3725 sg4046

lemma sg15956 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,4,1] := by
  exact rowSquare_join (by decide) sg3725 sg4047

lemma sg15957 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,5] := by
  exact rowSquare_join (by decide) sg3726 sg4047

lemma sg15958 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4263

lemma sg15959 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4142

lemma sg15960 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg4231

lemma sg15961 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4234

lemma sg15962 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,3] := by
  exact rowSquare_join (by decide) sg3360 sg4460

lemma sg15963 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4143

lemma sg15964 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg4235

lemma sg15965 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,3,2] := by
  exact rowSquare_join (by decide) sg3360 sg4461

lemma sg15966 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,4,1] := by
  exact rowSquare_join (by decide) sg3730 sg4043

lemma sg15967 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg4233

lemma sg15968 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,2,2] := by
  exact rowSquare_join (by decide) sg3360 sg4462

lemma sg15969 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,3,1] := by
  exact rowSquare_join (by decide) sg3725 sg4048

lemma sg15970 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,4] := by
  exact rowSquare_join (by decide) sg3726 sg4048

lemma sg15971 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,2,1] := by
  exact rowSquare_join (by decide) sg3725 sg4049

lemma sg15972 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,3] := by
  exact rowSquare_join (by decide) sg3726 sg4049

lemma sg15973 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2660 sg4966

lemma sg15974 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3251 sg4551

lemma sg15975 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15377

lemma sg15976 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3252 sg4544

lemma sg15977 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg3251 sg4552

lemma sg15978 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3363 sg4456

lemma sg15979 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3685 sg4144

lemma sg15980 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15378

lemma sg15981 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15379

lemma sg15982 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15380

lemma sg15983 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15381

lemma sg15984 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3252 sg4545

lemma sg15985 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg3251 sg4553

lemma sg15986 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3253 sg4544

lemma sg15987 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3252 sg4546

lemma sg15988 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15382

lemma sg15989 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3686 sg4144

lemma sg15990 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15383

lemma sg15991 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15384

lemma sg15992 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15385

lemma sg15993 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15386

lemma sg15994 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3254 sg4544

lemma sg15995 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3363 sg4457

lemma sg15996 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15387

lemma sg15997 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15388

lemma sg15998 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15389

lemma sg15999 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15390

lemma sg16000 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15391

lemma sg16001 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15392

lemma sg16002 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15393

lemma sg16003 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8 sg13509

lemma sg16004 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15394

lemma sg16005 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15395

lemma sg16006 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15396

lemma sg16007 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15397

lemma sg16008 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8 sg13512

lemma sg16009 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg0 sg15398

lemma sg16010 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg0 sg15399

lemma sg16011 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3253 sg4545

lemma sg16012 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3252 sg4549

lemma sg16013 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15400

lemma sg16014 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3254 sg4545

lemma sg16015 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3253 sg4546

lemma sg16016 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15401

lemma sg16017 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15402

lemma sg16018 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15403

lemma sg16019 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15404

lemma sg16020 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15405

lemma sg16021 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15406

lemma sg16022 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15407

lemma sg16023 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15408

lemma sg16024 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15409

lemma sg16025 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3254 sg4546

lemma sg16026 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15410

lemma sg16027 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15411

lemma sg16028 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15412

lemma sg16029 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15413

lemma sg16030 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15414

lemma sg16031 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15415

lemma sg16032 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15416

lemma sg16033 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg0 sg15417

lemma sg16034 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15418

lemma sg16035 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15419

lemma sg16036 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15420

lemma sg16037 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15421

lemma sg16038 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg0 sg15422

lemma sg16039 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg24 sg12723

lemma sg16040 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15423

lemma sg16041 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15424

lemma sg16042 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15425

lemma sg16043 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15426

lemma sg16044 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15427

lemma sg16045 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15428

lemma sg16046 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15429

lemma sg16047 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15430

lemma sg16048 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15431

lemma sg16049 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg22 sg12725

lemma sg16050 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15432

lemma sg16051 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15433

lemma sg16052 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg0 sg15434

lemma sg16053 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg22 sg12726

lemma sg16054 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,5,5] := by
  exact rowSquare_join (by decide) sg22 sg12727

lemma sg16055 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15435

lemma sg16056 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15436

lemma sg16057 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg0 sg15437

lemma sg16058 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,6,6,4] := by
  exact rowSquare_join (by decide) sg0 sg15438

lemma sg16059 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3566 sg4338

lemma sg16060 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3253 sg4549

lemma sg16061 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15439

lemma sg16062 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15440

lemma sg16063 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15441

lemma sg16064 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3254 sg4549

lemma sg16065 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15442

lemma sg16066 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15443

lemma sg16067 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15444

lemma sg16068 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15445

lemma sg16069 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15446

lemma sg16070 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15447

lemma sg16071 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15448

lemma sg16072 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg0 sg15449

lemma sg16073 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15450

lemma sg16074 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15451

lemma sg16075 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15452

lemma sg16076 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15453

lemma sg16077 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15454

lemma sg16078 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15455

lemma sg16079 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15456

lemma sg16080 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15457

lemma sg16081 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg22 sg12728

lemma sg16082 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15458

lemma sg16083 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15459

lemma sg16084 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg0 sg15460

lemma sg16085 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg23 sg12726

lemma sg16086 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,5,5,5] := by
  exact rowSquare_join (by decide) sg23 sg12727

lemma sg16087 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15461

lemma sg16088 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15462

lemma sg16089 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15463

lemma sg16090 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15464

lemma sg16091 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15465

lemma sg16092 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15466

lemma sg16093 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15467

lemma sg16094 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg22 sg12730

lemma sg16095 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg22 sg12731

lemma sg16096 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15468

lemma sg16097 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15469

lemma sg16098 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,3,1] := by
  exact rowSquare_join (by decide) sg22 sg12732

lemma sg16099 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,5,4] := by
  exact rowSquare_join (by decide) sg22 sg12733

lemma sg16100 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,2,1] := by
  exact rowSquare_join (by decide) sg0 sg15470

lemma sg16101 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,7,6,6,3] := by
  exact rowSquare_join (by decide) sg0 sg15471

lemma sg16102 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3568 sg4338

lemma sg16103 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3693 sg4138

lemma sg16104 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15472

lemma sg16105 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4264

lemma sg16106 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15473

lemma sg16107 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15474

lemma sg16108 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4265

lemma sg16109 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4147

lemma sg16110 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15475

lemma sg16111 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4148

lemma sg16112 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15476

lemma sg16113 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15477

lemma sg16114 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4266

lemma sg16115 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4149

lemma sg16116 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15478

lemma sg16117 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4145

lemma sg16118 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4150

lemma sg16119 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,8,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4146

lemma sg16120 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3646 sg4218

lemma sg16121 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15479

lemma sg16122 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [10,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15480

lemma sg16123 : RowSquare [5,5,4,3,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1943 sg6339

lemma sg16124 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1232 sg8016

lemma sg16125 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2137 sg5784

lemma sg16126 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2137 sg5785

lemma sg16127 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2139 sg5779

lemma sg16128 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1682 sg6515

lemma sg16129 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1232 sg8017

lemma sg16130 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1232 sg8018

lemma sg16131 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3359 sg4439

lemma sg16132 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2148 sg5776

lemma sg16133 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,4,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2645 sg4966

lemma sg16134 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2652 sg4965

lemma sg16135 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3302 sg4519

lemma sg16136 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2144 sg5780

lemma sg16137 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2654 sg4965

lemma sg16138 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2146 sg5778

lemma sg16139 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1682 sg6516

end UniversalTensorSquare
end
end

end OAI
