import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21

namespace OAI

/-! Semigroup Nodes 48. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19740 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,5,4] := by
  exact rowSquare_join (by decide) sg207 sg11615

lemma sg19741 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14362

lemma sg19742 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,6,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14363

lemma sg19743 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,6,3] := by
  exact rowSquare_join (by decide) sg13 sg14364

lemma sg19744 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,7,4,4] := by
  exact rowSquare_join (by decide) sg83 sg12562

lemma sg19745 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,7,5,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14365

lemma sg19746 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,7,5,2,1] := by
  exact rowSquare_join (by decide) sg40 sg12887

lemma sg19747 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,7,5,3] := by
  exact rowSquare_join (by decide) sg40 sg12888

lemma sg19748 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,7,6,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14366

lemma sg19749 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,7,6,2] := by
  exact rowSquare_join (by decide) sg13 sg14367

lemma sg19750 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12563

lemma sg19751 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14738

lemma sg19752 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,2,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12564

lemma sg19753 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14368

lemma sg19754 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,3,2,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11619

lemma sg19755 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,3,2,2] := by
  exact rowSquare_join (by decide) sg83 sg12565

lemma sg19756 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,3,3,1] := by
  exact rowSquare_join (by decide) sg83 sg12566

lemma sg19757 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,4,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11620

lemma sg19758 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,4,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11621

lemma sg19759 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,4,3] := by
  exact rowSquare_join (by decide) sg207 sg11622

lemma sg19760 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,5,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11623

lemma sg19761 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,8,5,2] := by
  exact rowSquare_join (by decide) sg207 sg11624

lemma sg19762 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3661 sg4059

lemma sg19763 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3399 sg4350

lemma sg19764 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3394 sg4351

lemma sg19765 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg3400 sg4350

lemma sg19766 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg270 sg11202

lemma sg19767 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15170

lemma sg19768 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3664 sg4051

lemma sg19769 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11202

lemma sg19770 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15171

lemma sg19771 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15172

lemma sg19772 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15173

lemma sg19773 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3665 sg4051

lemma sg19774 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15174

lemma sg19775 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15621

lemma sg19776 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3395 sg4351

lemma sg19777 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15175

lemma sg19778 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg3275 sg4510

lemma sg19779 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg0 sg15622

lemma sg19780 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15176

lemma sg19781 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15177

lemma sg19782 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3667 sg4051

lemma sg19783 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12889

lemma sg19784 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg270 sg11203

lemma sg19785 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15178

lemma sg19786 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15179

lemma sg19787 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3668 sg4051

lemma sg19788 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg271 sg11203

lemma sg19789 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14369

lemma sg19790 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15180

lemma sg19791 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3662 sg4057

lemma sg19792 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15181

lemma sg19793 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg3275 sg4511

lemma sg19794 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15182

lemma sg19795 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15183

lemma sg19796 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15184

lemma sg19797 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15185

lemma sg19798 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg41 sg12867

lemma sg19799 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12538

lemma sg19800 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11204

lemma sg19801 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15186

lemma sg19802 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3396 sg4351

lemma sg19803 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15187

lemma sg19804 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11204

lemma sg19805 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12890

lemma sg19806 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11205

lemma sg19807 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14370

lemma sg19808 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15188

lemma sg19809 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15189

lemma sg19810 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11206

lemma sg19811 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15190

lemma sg19812 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14739

lemma sg19813 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15191

lemma sg19814 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11205

lemma sg19815 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14371

lemma sg19816 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11206

lemma sg19817 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14372

lemma sg19818 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14373

lemma sg19819 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15192

lemma sg19820 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15193

lemma sg19821 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg6 sg14727

lemma sg19822 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg3666 sg4053

lemma sg19823 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12891

lemma sg19824 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15194

lemma sg19825 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15195

lemma sg19826 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15196

lemma sg19827 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg40 sg12889

lemma sg19828 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12539

lemma sg19829 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14335

lemma sg19830 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg270 sg11207

lemma sg19831 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3397 sg4351

lemma sg19832 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15197

lemma sg19833 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12540

lemma sg19834 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11207

lemma sg19835 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14374

lemma sg19836 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14375

lemma sg19837 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15198

lemma sg19838 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15199

lemma sg19839 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15200

lemma sg19840 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15201

lemma sg19841 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg5 sg14733

lemma sg19842 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15202

lemma sg19843 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12567

lemma sg19844 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12541

lemma sg19845 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12542

lemma sg19846 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14740

lemma sg19847 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg270 sg11208

lemma sg19848 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15203

lemma sg19849 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15204

lemma sg19850 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12543

lemma sg19851 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg271 sg11208

lemma sg19852 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12544

lemma sg19853 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11209

lemma sg19854 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14376

lemma sg19855 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15205

lemma sg19856 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11210

lemma sg19857 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14741

lemma sg19858 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12892

lemma sg19859 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11209

lemma sg19860 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14377

lemma sg19861 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11210

lemma sg19862 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14378

lemma sg19863 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg229 sg12335

lemma sg19864 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14379

lemma sg19865 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg5 sg14735

lemma sg19866 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg3545 sg4158

lemma sg19867 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12568

lemma sg19868 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg83 sg12569

lemma sg19869 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12545

lemma sg19870 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11625

lemma sg19871 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12570

lemma sg19872 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14742

lemma sg19873 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg270 sg11211

lemma sg19874 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15206

lemma sg19875 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12546

lemma sg19876 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11626

lemma sg19877 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11211

lemma sg19878 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11627

lemma sg19879 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg270 sg11212

lemma sg19880 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg229 sg12336

lemma sg19881 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11213

lemma sg19882 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14743

lemma sg19883 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12547

lemma sg19884 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12893

lemma sg19885 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg271 sg11212

lemma sg19886 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11213

lemma sg19887 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg270 sg11214

lemma sg19888 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg270 sg11215

lemma sg19889 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,5] := by
  exact rowSquare_join (by decide) sg270 sg11216

lemma sg19890 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14380

lemma sg19891 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14381

lemma sg19892 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11214

lemma sg19893 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg271 sg11215

lemma sg19894 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,4] := by
  exact rowSquare_join (by decide) sg271 sg11216

lemma sg19895 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg40 sg12891

lemma sg19896 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12548

lemma sg19897 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14337

lemma sg19898 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15207

lemma sg19899 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3398 sg4351

lemma sg19900 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15208

lemma sg19901 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12571

lemma sg19902 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12549

lemma sg19903 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12550

lemma sg19904 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14338

lemma sg19905 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14339

lemma sg19906 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15209

lemma sg19907 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg0 sg15623

lemma sg19908 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12551

lemma sg19909 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12552

lemma sg19910 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12895

lemma sg19911 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14382

lemma sg19912 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14383

lemma sg19913 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4891

lemma sg19914 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15624

lemma sg19915 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg5 sg14736

lemma sg19916 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12572

lemma sg19917 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg83 sg12573

lemma sg19918 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12553

lemma sg19919 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11630

lemma sg19920 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12574

lemma sg19921 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14340

lemma sg19922 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14341

lemma sg19923 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg15625

lemma sg19924 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12554

lemma sg19925 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11631

lemma sg19926 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11632

lemma sg19927 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11633

lemma sg19928 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14384

lemma sg19929 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg228 sg12337

lemma sg19930 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14342

lemma sg19931 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14744

lemma sg19932 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12555

lemma sg19933 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12896

lemma sg19934 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12556

lemma sg19935 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12557

lemma sg19936 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14385

lemma sg19937 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg14386

lemma sg19938 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,5] := by
  exact rowSquare_join (by decide) sg3309 sg4432

lemma sg19939 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12575

lemma sg19940 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12576

lemma sg19941 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12558

lemma sg19942 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11634

lemma sg19943 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11635

lemma sg19944 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12577

lemma sg19945 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14745

lemma sg19946 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg422 sg11546

lemma sg19947 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12559

lemma sg19948 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12560

lemma sg19949 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11636

lemma sg19950 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11637

lemma sg19951 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14387

lemma sg19952 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg4 sg14746

lemma sg19953 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12561

lemma sg19954 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12897

lemma sg19955 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11638

lemma sg19956 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,3,1] := by
  exact rowSquare_join (by decide) sg207 sg11639

lemma sg19957 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,4] := by
  exact rowSquare_join (by decide) sg207 sg11640

lemma sg19958 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14388

lemma sg19959 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,6,2,1] := by
  exact rowSquare_join (by decide) sg39 sg12898

lemma sg19960 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,6,3] := by
  exact rowSquare_join (by decide) sg39 sg12899

lemma sg19961 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg42 sg12875

lemma sg19962 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg40 sg12894

lemma sg19963 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12900

lemma sg19964 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14389

lemma sg19965 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14345

lemma sg19966 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14346

lemma sg19967 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15626

lemma sg19968 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg4892

lemma sg19969 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12578

lemma sg19970 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg83 sg12579

lemma sg19971 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12901

lemma sg19972 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11652

lemma sg19973 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12895

lemma sg19974 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14347

lemma sg19975 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14348

lemma sg19976 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4893

lemma sg19977 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12902

lemma sg19978 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12903

lemma sg19979 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12904

lemma sg19980 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14390

lemma sg19981 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14391

lemma sg19982 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg230 sg12335

lemma sg19983 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14349

lemma sg19984 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg3310 sg4428

lemma sg19985 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12580

lemma sg19986 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12581

lemma sg19987 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12582

lemma sg19988 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11653

lemma sg19989 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11654

lemma sg19990 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12583

lemma sg19991 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14350

lemma sg19992 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,3] := by
  exact rowSquare_join (by decide) sg423 sg11546

lemma sg19993 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12905

lemma sg19994 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12906

lemma sg19995 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11655

lemma sg19996 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11656

lemma sg19997 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14392

lemma sg19998 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,4,1] := by
  exact rowSquare_join (by decide) sg14 sg14352

lemma sg19999 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12907

lemma sg20000 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12908

lemma sg20001 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,2] := by
  exact rowSquare_join (by decide) sg208 sg11613

lemma sg20002 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,3,1] := by
  exact rowSquare_join (by decide) sg208 sg11614

lemma sg20003 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,4] := by
  exact rowSquare_join (by decide) sg208 sg11615

lemma sg20004 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12584

lemma sg20005 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg209 sg11610

lemma sg20006 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12585

lemma sg20007 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11658

lemma sg20008 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg209 sg11612

lemma sg20009 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg14356

lemma sg20010 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11659

lemma sg20011 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11100

lemma sg20012 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11661

lemma sg20013 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,3,1] := by
  exact rowSquare_join (by decide) sg207 sg11662

lemma sg20014 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,4] := by
  exact rowSquare_join (by decide) sg209 sg11615

lemma sg20015 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11101

lemma sg20016 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,5,2,1] := by
  exact rowSquare_join (by decide) sg364 sg11102

lemma sg20017 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,5,3] := by
  exact rowSquare_join (by decide) sg364 sg11103

lemma sg20018 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,6,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11104

lemma sg20019 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,6,2] := by
  exact rowSquare_join (by decide) sg364 sg11105

lemma sg20020 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg4301

lemma sg20021 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3392 sg4356

lemma sg20022 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg424 sg11545

lemma sg20023 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11674

lemma sg20024 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14361

lemma sg20025 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg424 sg11546

lemma sg20026 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14395

lemma sg20027 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14396

lemma sg20028 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14397

lemma sg20029 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,4,1] := by
  exact rowSquare_join (by decide) sg17 sg14552

lemma sg20030 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg3275 sg4512

lemma sg20031 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15210

lemma sg20032 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3275 sg4514

lemma sg20033 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15211

lemma sg20034 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg5 sg14739

lemma sg20035 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15212

lemma sg20036 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg489 sg8944

lemma sg20037 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg490 sg8944

lemma sg20038 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg489 sg8946

lemma sg20039 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg489 sg8947

lemma sg20040 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14398

lemma sg20041 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg490 sg8946

lemma sg20042 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg272 sg11214

lemma sg20043 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8947

lemma sg20044 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg272 sg11215

lemma sg20045 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg272 sg11216

lemma sg20046 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3275 sg4515

lemma sg20047 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15213

lemma sg20048 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14399

lemma sg20049 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15214

lemma sg20050 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg5 sg14741

lemma sg20051 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg270 sg11223

lemma sg20052 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg489 sg8948

lemma sg20053 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg271 sg11223

lemma sg20054 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg490 sg8948

lemma sg20055 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg489 sg8949

lemma sg20056 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11225

lemma sg20057 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,4,4,2] := by
  exact rowSquare_join (by decide) sg489 sg8950

lemma sg20058 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg271 sg11224

lemma sg20059 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11225

lemma sg20060 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg490 sg8949

lemma sg20061 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg490 sg8950

lemma sg20062 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,5,5,5] := by
  exact rowSquare_join (by decide) sg273 sg11216

lemma sg20063 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg274 sg11211

lemma sg20064 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg489 sg8951

lemma sg20065 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg422 sg11547

lemma sg20066 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg489 sg8952

lemma sg20067 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8951

lemma sg20068 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,4,3,2] := by
  exact rowSquare_join (by decide) sg489 sg8953

lemma sg20069 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,4,4,1] := by
  exact rowSquare_join (by decide) sg489 sg8954

lemma sg20070 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11108

lemma sg20071 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8952

lemma sg20072 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg489 sg8955

lemma sg20073 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg489 sg8956

lemma sg20074 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,5,4] := by
  exact rowSquare_join (by decide) sg490 sg8954

lemma sg20075 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11109

lemma sg20076 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,6,2,1] := by
  exact rowSquare_join (by decide) sg490 sg8955

lemma sg20077 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,6,6,6,3] := by
  exact rowSquare_join (by decide) sg490 sg8956

lemma sg20078 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15215

lemma sg20079 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14376

lemma sg20080 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15216

lemma sg20081 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg208 sg11632

lemma sg20082 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14400

lemma sg20083 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,4,4,3,3] := by
  exact rowSquare_join (by decide) sg229 sg12338

lemma sg20084 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14379

lemma sg20085 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,4,4,4,2] := by
  exact rowSquare_join (by decide) sg5 sg14744

lemma sg20086 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg275 sg11211

lemma sg20087 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg270 sg11226

lemma sg20088 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg15217

lemma sg20089 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg364 sg11110

lemma sg20090 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg275 sg11213

lemma sg20091 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,4,3,2] := by
  exact rowSquare_join (by decide) sg270 sg11227

lemma sg20092 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,4,4,1] := by
  exact rowSquare_join (by decide) sg270 sg11228

lemma sg20093 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11111

lemma sg20094 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11112

lemma sg20095 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,5,2,2] := by
  exact rowSquare_join (by decide) sg364 sg11113

lemma sg20096 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,5,3,1] := by
  exact rowSquare_join (by decide) sg364 sg11114

lemma sg20097 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,5,5,4] := by
  exact rowSquare_join (by decide) sg275 sg11216

lemma sg20098 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg276 sg11211

lemma sg20099 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg276 sg11212

lemma sg20100 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11229

lemma sg20101 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg14747

lemma sg20102 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11115

lemma sg20103 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg270 sg11230

lemma sg20104 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,4,2,2] := by
  exact rowSquare_join (by decide) sg364 sg11116

lemma sg20105 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,4,3,1] := by
  exact rowSquare_join (by decide) sg270 sg11231

lemma sg20106 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,4,4] := by
  exact rowSquare_join (by decide) sg270 sg11232

lemma sg20107 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11117

lemma sg20108 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,5,2,1] := by
  exact rowSquare_join (by decide) sg270 sg11233

lemma sg20109 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,5,3] := by
  exact rowSquare_join (by decide) sg270 sg11234

lemma sg20110 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,6,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11118

lemma sg20111 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,7,6,6,2] := by
  exact rowSquare_join (by decide) sg364 sg11119

lemma sg20112 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14383

lemma sg20113 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15218

lemma sg20114 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11704

lemma sg20115 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14384

lemma sg20116 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg15219

lemma sg20117 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg364 sg11120

lemma sg20118 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg208 sg11656

lemma sg20119 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,4,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14401

lemma sg20120 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,4,4,4,1] := by
  exact rowSquare_join (by decide) sg14 sg14386

lemma sg20121 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg209 sg11654

lemma sg20122 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg207 sg11705

lemma sg20123 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg209 sg11656

lemma sg20124 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg14387

lemma sg20125 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11121

lemma sg20126 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11122

lemma sg20127 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,4,2,2] := by
  exact rowSquare_join (by decide) sg364 sg11123

lemma sg20128 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,4,3,1] := by
  exact rowSquare_join (by decide) sg207 sg11706

lemma sg20129 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,4,4] := by
  exact rowSquare_join (by decide) sg210 sg11640

lemma sg20130 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11124

lemma sg20131 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,5,2,1] := by
  exact rowSquare_join (by decide) sg364 sg11125

lemma sg20132 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,5,5,3] := by
  exact rowSquare_join (by decide) sg364 sg11126

lemma sg20133 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg209 sg11658

lemma sg20134 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11127

lemma sg20135 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg365 sg11098

lemma sg20136 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,3,2,2] := by
  exact rowSquare_join (by decide) sg207 sg11707

lemma sg20137 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,3,3,1] := by
  exact rowSquare_join (by decide) sg209 sg11662

lemma sg20138 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg364 sg11128

lemma sg20139 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [10,8,6,4,2,1] := by
  exact rowSquare_join (by decide) sg364 sg11129

end UniversalTensorSquare
end
end

end OAI
