import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37

namespace OAI

/-! Semigroup Nodes 44. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg18140 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg16 sg13671

lemma sg18141 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,2] := by
  exact rowSquare_join (by decide) sg4 sg14652

lemma sg18142 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14037

lemma sg18143 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15554

lemma sg18144 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg39 sg12768

lemma sg18145 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14038

lemma sg18146 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12769

lemma sg18147 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg39 sg12770

lemma sg18148 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg39 sg12771

lemma sg18149 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg0 sg15555

lemma sg18150 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14653

lemma sg18151 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14040

lemma sg18152 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg14041

lemma sg18153 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg17 sg13671

lemma sg18154 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg14 sg14034

lemma sg18155 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12765

lemma sg18156 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg14654

lemma sg18157 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14042

lemma sg18158 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14043

lemma sg18159 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14044

lemma sg18160 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12767

lemma sg18161 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14045

lemma sg18162 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12769

lemma sg18163 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg40 sg12770

lemma sg18164 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg40 sg12771

lemma sg18165 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14046

lemma sg18166 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14047

lemma sg18167 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14048

lemma sg18168 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14049

lemma sg18169 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,4,1] := by
  exact rowSquare_join (by decide) sg13 sg14050

lemma sg18170 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg14051

lemma sg18171 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3631 sg4164

lemma sg18172 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14656

lemma sg18173 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14657

lemma sg18174 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3631 sg4167

lemma sg18175 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14052

lemma sg18176 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14053

lemma sg18177 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14658

lemma sg18178 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14659

lemma sg18179 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14660

lemma sg18180 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14661

lemma sg18181 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14054

lemma sg18182 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14055

lemma sg18183 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14056

lemma sg18184 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14057

lemma sg18185 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14058

lemma sg18186 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14059

lemma sg18187 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14662

lemma sg18188 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14663

lemma sg18189 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14060

lemma sg18190 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14664

lemma sg18191 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14061

lemma sg18192 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14062

lemma sg18193 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14063

lemma sg18194 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg14064

lemma sg18195 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg4 sg14665

lemma sg18196 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14666

lemma sg18197 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14065

lemma sg18198 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14066

lemma sg18199 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14067

lemma sg18200 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,4] := by
  exact rowSquare_join (by decide) sg13 sg14068

lemma sg18201 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14069

lemma sg18202 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg13 sg14070

lemma sg18203 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg14869

lemma sg18204 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14669

lemma sg18205 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg14649

lemma sg18206 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14071

lemma sg18207 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14072

lemma sg18208 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg2 sg14897

lemma sg18209 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg2 sg14900

lemma sg18210 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg14650

lemma sg18211 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14073

lemma sg18212 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14672

lemma sg18213 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14673

lemma sg18214 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg16 sg13689

lemma sg18215 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14074

lemma sg18216 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg39 sg12775

lemma sg18217 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg5 sg14652

lemma sg18218 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14075

lemma sg18219 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14674

lemma sg18220 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14035

lemma sg18221 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg17 sg13689

lemma sg18222 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg12861

lemma sg18223 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg12775

lemma sg18224 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14076

lemma sg18225 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg39 sg12785

lemma sg18226 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg39 sg12787

lemma sg18227 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,5,1] := by
  exact rowSquare_join (by decide) sg42 sg12771

lemma sg18228 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14675

lemma sg18229 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14039

lemma sg18230 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg13709

lemma sg18231 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg17 sg13711

lemma sg18232 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14676

lemma sg18233 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14077

lemma sg18234 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg14669

lemma sg18235 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14078

lemma sg18236 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14677

lemma sg18237 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg13772

lemma sg18238 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14079

lemma sg18239 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14080

lemma sg18240 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14071

lemma sg18241 : RowSquare [7,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg13772

lemma sg18242 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [4,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg656 sg10867

lemma sg18243 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [4,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg10867

lemma sg18244 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg661 sg10867

lemma sg18245 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg662 sg10867

lemma sg18246 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [5,5,5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg658 sg10871

lemma sg18247 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [5,5,5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg658 sg10873

lemma sg18248 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg663 sg10867

lemma sg18249 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg664 sg10867

lemma sg18250 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg659 sg10868

lemma sg18251 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg665 sg10867

lemma sg18252 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg660 sg10868

lemma sg18253 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg661 sg10868

lemma sg18254 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,4,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg659 sg10869

lemma sg18255 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg666 sg10867

lemma sg18256 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg662 sg10868

lemma sg18257 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,5,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg661 sg10869

lemma sg18258 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [6,6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg662 sg10869

lemma sg18259 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg667 sg10867

lemma sg18260 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg668 sg10867

lemma sg18261 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg663 sg10868

lemma sg18262 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg664 sg10868

lemma sg18263 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg669 sg10867

lemma sg18264 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg665 sg10868

lemma sg18265 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg664 sg10869

lemma sg18266 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg666 sg10868

lemma sg18267 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg665 sg10869

lemma sg18268 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,5,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg661 sg10875

lemma sg18269 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg666 sg10869

lemma sg18270 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,6,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg666 sg10870

lemma sg18271 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [7,6,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg662 sg10875

lemma sg18272 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg670 sg10867

lemma sg18273 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [9,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg671 sg10867

lemma sg18274 : RowSquare [7,6,2,2,2,2,2,2,2,2,1,1] [10,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg672 sg10867

lemma sg18275 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4937

lemma sg18276 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2629 sg4940

lemma sg18277 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3354 sg4421

lemma sg18278 : RowSquare [7,6,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14085

lemma sg18279 : RowSquare [7,6,3,2,2,2,2,2,2,2,1] [6,6,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg11533

lemma sg18280 : RowSquare [7,6,3,2,2,2,2,2,2,2,1] [6,6,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg11534

lemma sg18281 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4877

lemma sg18282 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4878

lemma sg18283 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3320 sg4162

lemma sg18284 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3320 sg4165

lemma sg18285 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2628 sg4877

lemma sg18286 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2628 sg4878

lemma sg18287 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3325 sg4163

lemma sg18288 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2635 sg4876

lemma sg18289 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg15597

lemma sg18290 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [6,6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg2640 sg4879

lemma sg18291 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [6,6,6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg4 sg14700

lemma sg18292 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [6,6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg3332 sg4173

lemma sg18293 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3732 sg3858

lemma sg18294 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [7,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14702

lemma sg18295 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg0 sg15598

lemma sg18296 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg14110

lemma sg18297 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg762 sg8076

lemma sg18298 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11152

lemma sg18299 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [7,7,7,6,4] := by
  exact rowSquare_join (by decide) sg762 sg8077

lemma sg18300 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11153

lemma sg18301 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg490 sg8898

lemma sg18302 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg490 sg8899

lemma sg18303 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg15 sg14089

lemma sg18304 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg14699

lemma sg18305 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg13 sg14112

lemma sg18306 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14703

lemma sg18307 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,6,6,6,5] := by
  exact rowSquare_join (by decide) sg762 sg8080

lemma sg18308 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg14 sg14109

lemma sg18309 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,7,6,5,5] := by
  exact rowSquare_join (by decide) sg762 sg8084

lemma sg18310 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg762 sg8085

lemma sg18311 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,7,7,5,4] := by
  exact rowSquare_join (by decide) sg841 sg8026

lemma sg18312 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,7,7,6,1,1,1] := by
  exact rowSquare_join (by decide) sg839 sg8028

lemma sg18313 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,7,7,6,2,1] := by
  exact rowSquare_join (by decide) sg840 sg8027

lemma sg18314 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,7,7,6,3] := by
  exact rowSquare_join (by decide) sg841 sg8027

lemma sg18315 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,7,7,7,1,1] := by
  exact rowSquare_join (by decide) sg840 sg8028

lemma sg18316 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,7,7,7,2] := by
  exact rowSquare_join (by decide) sg841 sg8028

lemma sg18317 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,5,5,5] := by
  exact rowSquare_join (by decide) sg762 sg8090

lemma sg18318 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,6,5,4] := by
  exact rowSquare_join (by decide) sg841 sg8030

lemma sg18319 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg271 sg11160

lemma sg18320 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,6,6,2,1] := by
  exact rowSquare_join (by decide) sg840 sg8031

lemma sg18321 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,6,6,3] := by
  exact rowSquare_join (by decide) sg841 sg8031

lemma sg18322 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,7,4,4] := by
  exact rowSquare_join (by decide) sg841 sg8032

lemma sg18323 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,7,5,1,1,1] := by
  exact rowSquare_join (by decide) sg839 sg8034

lemma sg18324 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,7,5,2,1] := by
  exact rowSquare_join (by decide) sg840 sg8033

lemma sg18325 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,7,5,3] := by
  exact rowSquare_join (by decide) sg841 sg8033

lemma sg18326 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,7,6,1,1] := by
  exact rowSquare_join (by decide) sg840 sg8034

lemma sg18327 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,7,6,2] := by
  exact rowSquare_join (by decide) sg841 sg8034

lemma sg18328 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,7,7,1] := by
  exact rowSquare_join (by decide) sg490 sg8903

lemma sg18329 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12465

lemma sg18330 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11593

lemma sg18331 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg496 sg8896

lemma sg18332 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,2,2,2,1] := by
  exact rowSquare_join (by decide) sg839 sg8035

lemma sg18333 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg496 sg8897

lemma sg18334 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,3,2,1,1] := by
  exact rowSquare_join (by decide) sg839 sg8036

lemma sg18335 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,3,2,2] := by
  exact rowSquare_join (by decide) sg840 sg8035

lemma sg18336 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,3,3,1] := by
  exact rowSquare_join (by decide) sg841 sg8035

lemma sg18337 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,4,1,1,1] := by
  exact rowSquare_join (by decide) sg839 sg8037

lemma sg18338 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,4,2,1] := by
  exact rowSquare_join (by decide) sg840 sg8036

lemma sg18339 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,4,3] := by
  exact rowSquare_join (by decide) sg841 sg8036

lemma sg18340 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,5,1,1] := by
  exact rowSquare_join (by decide) sg840 sg8037

lemma sg18341 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,5,2] := by
  exact rowSquare_join (by decide) sg841 sg8037

lemma sg18342 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,6,1] := by
  exact rowSquare_join (by decide) sg490 sg8904

lemma sg18343 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [8,8,8,7] := by
  exact rowSquare_join (by decide) sg271 sg11161

lemma sg18344 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg15 sg14090

lemma sg18345 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg15 sg14091

lemma sg18346 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg14092

lemma sg18347 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg43 sg12834

lemma sg18348 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg15 sg14093

lemma sg18349 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg14094

lemma sg18350 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg41 sg12837

lemma sg18351 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg41 sg12838

lemma sg18352 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg41 sg12839

lemma sg18353 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14116

lemma sg18354 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12459

lemma sg18355 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12460

lemma sg18356 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg272 sg11154

lemma sg18357 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg39 sg12854

lemma sg18358 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg44 sg12833

lemma sg18359 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg14095

lemma sg18360 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg14096

lemma sg18361 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg15 sg14097

lemma sg18362 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg15058

lemma sg18363 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6 sg14701

lemma sg18364 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg15 sg14098

lemma sg18365 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14111

lemma sg18366 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg42 sg12837

lemma sg18367 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg42 sg12838

lemma sg18368 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg42 sg12839

lemma sg18369 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14117

lemma sg18370 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg40 sg12852

lemma sg18371 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12853

lemma sg18372 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg272 sg11155

lemma sg18373 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg40 sg12854

lemma sg18374 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg116 sg11724

lemma sg18375 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12461

lemma sg18376 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg273 sg11154

lemma sg18377 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12462

lemma sg18378 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg272 sg11156

lemma sg18379 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg39 sg12856

lemma sg18380 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg12835

lemma sg18381 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg43 sg12836

lemma sg18382 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg15 sg14099

lemma sg18383 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg15 sg14100

lemma sg18384 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg15 sg14101

lemma sg18385 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg110 sg11727

lemma sg18386 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg242 sg11167

lemma sg18387 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12466

lemma sg18388 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg455 sg8923

lemma sg18389 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12467

lemma sg18390 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg460 sg8912

lemma sg18391 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg41 sg12843

lemma sg18392 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1131 sg6707

lemma sg18393 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg456 sg8923

lemma sg18394 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg11594

lemma sg18395 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg455 sg8924

lemma sg18396 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg489 sg8905

lemma sg18397 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg460 sg8913

lemma sg18398 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg12844

lemma sg18399 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg762 sg8091

lemma sg18400 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg41 sg12845

lemma sg18401 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg41 sg12846

lemma sg18402 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14704

lemma sg18403 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg11168

lemma sg18404 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg456 sg8924

lemma sg18405 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg11169

lemma sg18406 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg490 sg8905

lemma sg18407 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg277 sg11150

lemma sg18408 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg460 sg8914

lemma sg18409 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg762 sg8092

lemma sg18410 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg762 sg8093

lemma sg18411 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg84 sg12463

lemma sg18412 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg762 sg8094

lemma sg18413 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg15 sg14102

lemma sg18414 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14118

lemma sg18415 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg42 sg12840

lemma sg18416 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg42 sg12841

lemma sg18417 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg272 sg11157

lemma sg18418 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg42 sg12842

lemma sg18419 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg111 sg11727

lemma sg18420 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg240 sg11170

lemma sg18421 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg85 sg12453

lemma sg18422 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg455 sg8925

lemma sg18423 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12855

lemma sg18424 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg460 sg8915

lemma sg18425 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg40 sg12856

lemma sg18426 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg116 sg11725

lemma sg18427 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg456 sg8925

lemma sg18428 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12464

lemma sg18429 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg457 sg8924

lemma sg18430 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg460 sg8916

lemma sg18431 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg460 sg8917

lemma sg18432 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg85 sg12454

lemma sg18433 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg762 sg8095

lemma sg18434 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg85 sg12455

lemma sg18435 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg85 sg12456

lemma sg18436 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg14 sg14112

lemma sg18437 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg239 sg11171

lemma sg18438 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11172

lemma sg18439 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg458 sg8923

lemma sg18440 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12468

lemma sg18441 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg455 sg8926

lemma sg18442 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8038

lemma sg18443 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg460 sg8918

lemma sg18444 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1131 sg6708

lemma sg18445 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1131 sg6709

lemma sg18446 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg243 sg11169

lemma sg18447 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8039

lemma sg18448 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg455 sg8927

lemma sg18449 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg489 sg8906

lemma sg18450 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8040

lemma sg18451 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg762 sg8096

lemma sg18452 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg40 sg12857

lemma sg18453 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg11589

lemma sg18454 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8041

lemma sg18455 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg456 sg8927

lemma sg18456 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8042

lemma sg18457 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg491 sg8900

lemma sg18458 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg491 sg8901

lemma sg18459 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg762 sg8097

lemma sg18460 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg762 sg8098

lemma sg18461 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg762 sg8099

lemma sg18462 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11173

lemma sg18463 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg459 sg8923

lemma sg18464 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11174

lemma sg18465 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg462 sg8912

lemma sg18466 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11175

lemma sg18467 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg842 sg8024

lemma sg18468 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg455 sg8928

lemma sg18469 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg839 sg8038

lemma sg18470 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1131 sg6710

lemma sg18471 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg842 sg8025

lemma sg18472 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1131 sg6711

lemma sg18473 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg842 sg8026

lemma sg18474 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg839 sg8039

lemma sg18475 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg840 sg8038

lemma sg18476 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg839 sg8040

lemma sg18477 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg763 sg8078

lemma sg18478 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1131 sg6712

lemma sg18479 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg842 sg8027

lemma sg18480 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg1131 sg6713

lemma sg18481 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1131 sg6714

lemma sg18482 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg840 sg8039

lemma sg18483 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg840 sg8040

lemma sg18484 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,5,5] := by
  exact rowSquare_join (by decide) sg841 sg8040

lemma sg18485 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg842 sg8028

lemma sg18486 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg764 sg8079

lemma sg18487 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg840 sg8041

lemma sg18488 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg840 sg8042

lemma sg18489 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,6,6,6,4] := by
  exact rowSquare_join (by decide) sg841 sg8042

lemma sg18490 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14113

lemma sg18491 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg241 sg11170

lemma sg18492 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg85 sg12457

lemma sg18493 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg457 sg8925

lemma sg18494 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg12847

lemma sg18495 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg272 sg11158

lemma sg18496 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg42 sg12848

lemma sg18497 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg239 sg11177

lemma sg18498 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg240 sg11172

lemma sg18499 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg458 sg8925

lemma sg18500 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg85 sg12458

lemma sg18501 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg455 sg8929

lemma sg18502 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8043

lemma sg18503 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg272 sg11159

lemma sg18504 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg244 sg11168

lemma sg18505 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg456 sg8929

lemma sg18506 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg244 sg11169

lemma sg18507 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8044

lemma sg18508 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg457 sg8927

lemma sg18509 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg491 sg8902

lemma sg18510 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8045

lemma sg18511 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg762 sg8100

lemma sg18512 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg42 sg12849

lemma sg18513 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11178

lemma sg18514 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg459 sg8925

lemma sg18515 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11179

lemma sg18516 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg458 sg8926

lemma sg18517 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11180

lemma sg18518 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8046

lemma sg18519 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg455 sg8930

lemma sg18520 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg839 sg8043

lemma sg18521 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg240 sg11176

lemma sg18522 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1131 sg6715

lemma sg18523 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg456 sg8930

lemma sg18524 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8047

lemma sg18525 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg839 sg8044

lemma sg18526 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg840 sg8043

lemma sg18527 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg839 sg8045

lemma sg18528 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg763 sg8082

lemma sg18529 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg208 sg11591

lemma sg18530 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8048

lemma sg18531 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg765 sg8079

lemma sg18532 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg762 sg8101

lemma sg18533 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg840 sg8044

lemma sg18534 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg840 sg8045

lemma sg18535 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,5,5,5] := by
  exact rowSquare_join (by decide) sg841 sg8045

lemma sg18536 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11181

lemma sg18537 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg838 sg8049

lemma sg18538 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg11182

lemma sg18539 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,7,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg838 sg8050

end UniversalTensorSquare
end
end

end OAI
