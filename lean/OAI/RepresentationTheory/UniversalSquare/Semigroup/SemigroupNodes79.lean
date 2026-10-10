import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes78
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes42
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes45

namespace OAI

/-! Semigroup Nodes 79. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg32141 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17190

lemma sg32142 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16670

lemma sg32143 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17190

lemma sg32144 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17182

lemma sg32145 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17182

lemma sg32146 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16663

lemma sg32147 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,8,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14312 sg21345

lemma sg32148 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,8,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20439

lemma sg32149 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,8,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14310 sg21348

lemma sg32150 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,8,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15224 sg21194

lemma sg32151 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,8,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17181

lemma sg32152 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,8,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17182

lemma sg32153 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15644 sg20985

lemma sg32154 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20440

lemma sg32155 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15610 sg21053

lemma sg32156 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17185

lemma sg32157 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16232

lemma sg32158 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17185

lemma sg32159 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15611 sg21053

lemma sg32160 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16232

lemma sg32161 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17149 sg20542

lemma sg32162 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17183

lemma sg32163 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17317

lemma sg32164 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18296

lemma sg32165 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17317

lemma sg32166 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18296

lemma sg32167 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18281 sg20356

lemma sg32168 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18296

lemma sg32169 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg16649 sg20661

lemma sg32170 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18282 sg20356

lemma sg32171 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18296

lemma sg32172 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20557

lemma sg32173 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18296

lemma sg32174 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg16650 sg20661

lemma sg32175 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17212

lemma sg32176 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20795 sg16158

lemma sg32177 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20505 sg17212

lemma sg32178 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17211

lemma sg32179 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18284 sg20338

lemma sg32180 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17211

lemma sg32181 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20696 sg16234

lemma sg32182 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16234

lemma sg32183 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20517 sg17187

lemma sg32184 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17186

lemma sg32185 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18029

lemma sg32186 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16688

lemma sg32187 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18285 sg20338

lemma sg32188 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17211

lemma sg32189 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18286 sg20338

lemma sg32190 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20647 sg16654

lemma sg32191 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17212

lemma sg32192 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18284 sg20339

lemma sg32193 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17212

lemma sg32194 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18030

lemma sg32195 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16689

lemma sg32196 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18285 sg20339

lemma sg32197 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17212

lemma sg32198 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18286 sg20339

lemma sg32199 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17188

lemma sg32200 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16235

lemma sg32201 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17188

lemma sg32202 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19620 sg19180

lemma sg32203 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16235

lemma sg32204 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17149 sg20543

lemma sg32205 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20696 sg16237

lemma sg32206 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16237

lemma sg32207 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20517 sg17190

lemma sg32208 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17189

lemma sg32209 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16236

lemma sg32210 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17189

lemma sg32211 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17184

lemma sg32212 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16236

lemma sg32213 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17149 sg20544

lemma sg32214 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16665

lemma sg32215 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17190

lemma sg32216 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16237

lemma sg32217 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17190

lemma sg32218 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16237

lemma sg32219 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17149 sg20545

lemma sg32220 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16666

lemma sg32221 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,8,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12864 sg21635

lemma sg32222 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,8,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15225 sg21194

lemma sg32223 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,8,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15604 sg21076

lemma sg32224 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,8,8,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17185

lemma sg32225 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20649 sg16652

lemma sg32226 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg15665 sg20953

lemma sg32227 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20504 sg17213

lemma sg32228 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20795 sg16159

lemma sg32229 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20505 sg17213

lemma sg32230 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17186

lemma sg32231 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg15666 sg20951

lemma sg32232 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20741 sg16217

lemma sg32233 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20649 sg16654

lemma sg32234 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17186

lemma sg32235 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15671 sg20947

lemma sg32236 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17186

lemma sg32237 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20506 sg17213

lemma sg32238 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18284 sg20340

lemma sg32239 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20507 sg17213

lemma sg32240 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20498 sg18031

lemma sg32241 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20633 sg16690

lemma sg32242 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18285 sg20340

lemma sg32243 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17213

lemma sg32244 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg18286 sg20340

lemma sg32245 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17188

lemma sg32246 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17188

lemma sg32247 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17188

lemma sg32248 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20650 sg16654

lemma sg32249 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17187

lemma sg32250 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20441

lemma sg32251 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20742 sg16218

lemma sg32252 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17189

lemma sg32253 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17189

lemma sg32254 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17189

lemma sg32255 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17187

lemma sg32256 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17188

lemma sg32257 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17188

lemma sg32258 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16668

lemma sg32259 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17190

lemma sg32260 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17190

lemma sg32261 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17190

lemma sg32262 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17189

lemma sg32263 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17189

lemma sg32264 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16669

lemma sg32265 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17190

lemma sg32266 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17190

lemma sg32267 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17190

lemma sg32268 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16670

lemma sg32269 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,8,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5731 sg31939

lemma sg32270 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,8,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17190

lemma sg32271 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,9,9,9,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5731 sg31940

lemma sg32272 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18275 sg20420

lemma sg32273 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18122

lemma sg32274 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20323 sg18292

lemma sg32275 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16677

lemma sg32276 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20324 sg18292

lemma sg32277 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16677

lemma sg32278 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20325 sg18292

lemma sg32279 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16245

lemma sg32280 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17149 sg20546

lemma sg32281 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17191

lemma sg32282 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17342

lemma sg32283 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18297

lemma sg32284 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17342

lemma sg32285 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18297

lemma sg32286 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18281 sg20358

lemma sg32287 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18297

lemma sg32288 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg16649 sg20663

lemma sg32289 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18282 sg20358

lemma sg32290 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18297

lemma sg32291 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20558

lemma sg32292 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18297

lemma sg32293 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg16650 sg20663

lemma sg32294 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17192

lemma sg32295 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20425 sg18117

lemma sg32296 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20754 sg16209

lemma sg32297 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17201

lemma sg32298 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18124

lemma sg32299 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17201

lemma sg32300 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17200

lemma sg32301 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18123

lemma sg32302 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17200

lemma sg32303 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17193

lemma sg32304 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16678

lemma sg32305 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20883 sg15698

lemma sg32306 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16671

lemma sg32307 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17200

lemma sg32308 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16678

lemma sg32309 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17200

lemma sg32310 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17202

lemma sg32311 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18125

lemma sg32312 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17202

lemma sg32313 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17201

lemma sg32314 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18124

lemma sg32315 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17201

lemma sg32316 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17194

lemma sg32317 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17194

lemma sg32318 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16679

lemma sg32319 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17201

lemma sg32320 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16679

lemma sg32321 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17201

lemma sg32322 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20883 sg15699

lemma sg32323 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20884 sg15699

lemma sg32324 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17202

lemma sg32325 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18125

lemma sg32326 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17202

lemma sg32327 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16680

lemma sg32328 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17202

lemma sg32329 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16680

lemma sg32330 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17202

lemma sg32331 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17195

lemma sg32332 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17195

lemma sg32333 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16672

lemma sg32334 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17150 sg20546

lemma sg32335 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18920 sg19626

lemma sg32336 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg15668 sg20950

lemma sg32337 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20326 sg18291

lemma sg32338 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20327 sg18291

lemma sg32339 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16673

lemma sg32340 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,8,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14313 sg21345

lemma sg32341 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,8,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14765 sg21269

lemma sg32342 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,8,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15613 sg21051

lemma sg32343 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,8,8,8,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14725 sg21270

lemma sg32344 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20499 sg17347

lemma sg32345 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18299

lemma sg32346 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17347

lemma sg32347 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18909 sg19657

lemma sg32348 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18910 sg19657

lemma sg32349 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18299

lemma sg32350 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19657

lemma sg32351 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18912 sg19657

lemma sg32352 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18299

lemma sg32353 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19657

lemma sg32354 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18299

lemma sg32355 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg18914 sg19657

lemma sg32356 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20691 sg16266

lemma sg32357 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20796 sg16158

lemma sg32358 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20509 sg17212

lemma sg32359 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17209

lemma sg32360 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18129

lemma sg32361 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17209

lemma sg32362 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17208

lemma sg32363 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18128

lemma sg32364 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17208

lemma sg32365 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17197

lemma sg32366 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20696 sg16249

lemma sg32367 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16249

lemma sg32368 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20517 sg17199

lemma sg32369 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17208

lemma sg32370 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16685

lemma sg32371 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17208

lemma sg32372 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17210

lemma sg32373 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18130

lemma sg32374 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17210

lemma sg32375 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17209

lemma sg32376 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18129

lemma sg32377 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17209

lemma sg32378 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16248

lemma sg32379 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17198

lemma sg32380 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16686

lemma sg32381 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17209

lemma sg32382 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16686

lemma sg32383 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17209

lemma sg32384 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16249

lemma sg32385 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18287 sg20331

lemma sg32386 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17210

lemma sg32387 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18130

lemma sg32388 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17210

lemma sg32389 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16687

lemma sg32390 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17210

lemma sg32391 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16687

lemma sg32392 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17210

lemma sg32393 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16250

lemma sg32394 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18287 sg20332

lemma sg32395 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16674

lemma sg32396 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17148 sg20547

lemma sg32397 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16251

lemma sg32398 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20424 sg18122

lemma sg32399 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,7,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16251

lemma sg32400 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17149 sg20547

lemma sg32401 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,7,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17196

lemma sg32402 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20791 sg16191

lemma sg32403 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20827 sg16128

lemma sg32404 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20691 sg16267

lemma sg32405 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20796 sg16159

lemma sg32406 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20509 sg17213

lemma sg32407 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17211

lemma sg32408 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18131

lemma sg32409 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17211

lemma sg32410 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20696 sg16252

lemma sg32411 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16252

lemma sg32412 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20517 sg17200

lemma sg32413 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17197

lemma sg32414 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17212

lemma sg32415 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18132

lemma sg32416 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17212

lemma sg32417 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17211

lemma sg32418 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18131

lemma sg32419 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17211

lemma sg32420 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16252

lemma sg32421 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17200

lemma sg32422 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16688

lemma sg32423 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17211

lemma sg32424 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16688

lemma sg32425 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17211

lemma sg32426 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17212

lemma sg32427 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18132

lemma sg32428 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17212

lemma sg32429 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16689

lemma sg32430 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17212

lemma sg32431 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16689

lemma sg32432 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17212

lemma sg32433 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16253

lemma sg32434 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18287 sg20333

lemma sg32435 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16675

lemma sg32436 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17202

lemma sg32437 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16254

lemma sg32438 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20519 sg17202

lemma sg32439 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20700 sg16254

lemma sg32440 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18287 sg20334

lemma sg32441 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16676

lemma sg32442 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17150 sg20547

lemma sg32443 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20326 sg18292

lemma sg32444 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20327 sg18292

lemma sg32445 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16677

lemma sg32446 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,8,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14313 sg21346

lemma sg32447 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,8,8,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14725 sg21271

lemma sg32448 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15683 sg20898

lemma sg32449 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20827 sg16130

lemma sg32450 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg15682 sg20901

lemma sg32451 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20510 sg17213

lemma sg32452 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20422 sg18133

lemma sg32453 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20511 sg17213

lemma sg32454 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17200

lemma sg32455 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20827 sg16131

lemma sg32456 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15667 sg20951

lemma sg32457 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17200

lemma sg32458 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17200

lemma sg32459 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20512 sg17213

lemma sg32460 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20423 sg18133

lemma sg32461 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20513 sg17213

lemma sg32462 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20634 sg16690

lemma sg32463 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20515 sg17213

lemma sg32464 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20635 sg16690

lemma sg32465 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20516 sg17213

lemma sg32466 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20651 sg16655

lemma sg32467 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16678

lemma sg32468 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17202

lemma sg32469 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17202

lemma sg32470 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20522 sg17202

lemma sg32471 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17201

lemma sg32472 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17201

lemma sg32473 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16679

lemma sg32474 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20523 sg17202

lemma sg32475 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20524 sg17202

lemma sg32476 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20525 sg17202

lemma sg32477 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20636 sg16680

lemma sg32478 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15672 sg20950

lemma sg32479 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20526 sg17202

lemma sg32480 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,9,9,8,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5731 sg31941

lemma sg32481 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18300

lemma sg32482 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16255

lemma sg32483 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg20698 sg16255

lemma sg32484 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20828 sg16126

lemma sg32485 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17348

lemma sg32486 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18300

lemma sg32487 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16255

lemma sg32488 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20693 sg16256

lemma sg32489 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20694 sg16256

lemma sg32490 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20695 sg16256

lemma sg32491 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18281 sg20361

lemma sg32492 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18300

lemma sg32493 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20756 sg16210

lemma sg32494 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18282 sg20361

lemma sg32495 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18300

lemma sg32496 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20559

lemma sg32497 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18300

lemma sg32498 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg20756 sg16211

lemma sg32499 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15608 sg21057

lemma sg32500 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15599 sg21078

lemma sg32501 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15642 sg20991

lemma sg32502 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg15638 sg21041

lemma sg32503 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20683 sg16384

lemma sg32504 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg20314 sg18301

lemma sg32505 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20520 sg17203

lemma sg32506 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20757 sg16210

lemma sg32507 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20521 sg17203

lemma sg32508 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20693 sg16258

lemma sg32509 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20694 sg16258

lemma sg32510 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg20695 sg16258

lemma sg32511 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20500 sg17349

lemma sg32512 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20315 sg18301

lemma sg32513 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18281 sg20362

lemma sg32514 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18301

lemma sg32515 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg16649 sg20664

lemma sg32516 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18282 sg20362

lemma sg32517 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20317 sg18301

lemma sg32518 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17147 sg20560

lemma sg32519 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20318 sg18301

lemma sg32520 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg16650 sg20664

lemma sg32521 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20693 sg16260

lemma sg32522 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20694 sg16260

lemma sg32523 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20695 sg16260

lemma sg32524 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20696 sg16257

lemma sg32525 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20697 sg16257

lemma sg32526 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20517 sg17204

lemma sg32527 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20756 sg16213

lemma sg32528 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15637 sg21042

lemma sg32529 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg15656 sg20961

lemma sg32530 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15607 sg21058

lemma sg32531 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg18115 sg20442

lemma sg32532 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg15594 sg21085

lemma sg32533 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20693 sg16261

lemma sg32534 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg20694 sg16261

lemma sg32535 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg20695 sg16261

lemma sg32536 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15608 sg21058

lemma sg32537 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20699 sg16256

lemma sg32538 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15677 sg20903

lemma sg32539 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg20424 sg18126

lemma sg32540 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,10,10,5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20518 sg17204

end UniversalTensorSquare
end
end

end OAI
