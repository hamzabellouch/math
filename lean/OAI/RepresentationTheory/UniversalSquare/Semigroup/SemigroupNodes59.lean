import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes52
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24

namespace OAI

/-! Semigroup Nodes 59. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg24140 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg8546 sg10086

lemma sg24141 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9477

lemma sg24142 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10305

lemma sg24143 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10113

lemma sg24144 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9749

lemma sg24145 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8347 sg10635

lemma sg24146 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9477

lemma sg24147 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10306

lemma sg24148 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10243

lemma sg24149 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9750

lemma sg24150 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9723

lemma sg24151 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10636

lemma sg24152 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8861 sg8999

lemma sg24153 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10114

lemma sg24154 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9751

lemma sg24155 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9724

lemma sg24156 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10227

lemma sg24157 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9464

lemma sg24158 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8533 sg10097

lemma sg24159 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9465

lemma sg24160 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9465

lemma sg24161 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8442 sg10193

lemma sg24162 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10623

lemma sg24163 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg8655 sg9669

lemma sg24164 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10307

lemma sg24165 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10244

lemma sg24166 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9752

lemma sg24167 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9725

lemma sg24168 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10228

lemma sg24169 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9466

lemma sg24170 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8861 sg9000

lemma sg24171 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9726

lemma sg24172 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10229

lemma sg24173 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9467

lemma sg24174 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9467

lemma sg24175 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9001

lemma sg24176 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10624

lemma sg24177 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8432 sg10217

lemma sg24178 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10625

lemma sg24179 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg8655 sg9671

lemma sg24180 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8531 sg10098

lemma sg24181 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10098

lemma sg24182 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg8533 sg10098

lemma sg24183 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8538 sg10091

lemma sg24184 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg8539 sg10090

lemma sg24185 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg7243 sg11439

lemma sg24186 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg8863 sg8994

lemma sg24187 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg8431 sg10219

lemma sg24188 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg8549 sg10086

lemma sg24189 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5260 sg12681

lemma sg24190 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10230

lemma sg24191 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8385 sg10597

lemma sg24192 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8757 sg9444

lemma sg24193 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10115

lemma sg24194 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8735 sg9456

lemma sg24195 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10195

lemma sg24196 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9727

lemma sg24197 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9727

lemma sg24198 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10230

lemma sg24199 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9468

lemma sg24200 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9468

lemma sg24201 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9002

lemma sg24202 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8371 sg10601

lemma sg24203 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8439 sg10195

lemma sg24204 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8440 sg10195

lemma sg24205 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8441 sg10195

lemma sg24206 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8442 sg10195

lemma sg24207 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8540 sg10091

lemma sg24208 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8430 sg10221

lemma sg24209 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg7244 sg11439

lemma sg24210 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8351 sg10625

lemma sg24211 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg8656 sg9671

lemma sg24212 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8484 sg10172

lemma sg24213 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8462 sg10182

lemma sg24214 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg8352 sg10624

lemma sg24215 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg8352 sg10625

lemma sg24216 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg8431 sg10221

lemma sg24217 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg8550 sg10086

lemma sg24218 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg332 sg21316

lemma sg24219 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg332 sg21317

lemma sg24220 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg561 sg21232

lemma sg24221 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,6,6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg561 sg21233

lemma sg24222 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8758 sg9441

lemma sg24223 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8524 sg10116

lemma sg24224 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg7232 sg11452

lemma sg24225 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9481

lemma sg24226 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8742 sg9446

lemma sg24227 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10117

lemma sg24228 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8839 sg9157

lemma sg24229 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9457

lemma sg24230 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8720 sg9482

lemma sg24231 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10118

lemma sg24232 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9753

lemma sg24233 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8820 sg9160

lemma sg24234 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8808 sg9166

lemma sg24235 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10119

lemma sg24236 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9754

lemma sg24237 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8730 sg9458

lemma sg24238 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8810 sg9166

lemma sg24239 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9026

lemma sg24240 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9483

lemma sg24241 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8809 sg9167

lemma sg24242 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10222

lemma sg24243 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9027

lemma sg24244 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8447 sg10190

lemma sg24245 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9481

lemma sg24246 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8720 sg9484

lemma sg24247 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10120

lemma sg24248 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9755

lemma sg24249 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8823 sg9160

lemma sg24250 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9481

lemma sg24251 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9482

lemma sg24252 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10121

lemma sg24253 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9756

lemma sg24254 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8733 sg9458

lemma sg24255 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9161

lemma sg24256 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9028

lemma sg24257 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10122

lemma sg24258 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9757

lemma sg24259 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9485

lemma sg24260 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8809 sg9169

lemma sg24261 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10223

lemma sg24262 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9029

lemma sg24263 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9486

lemma sg24264 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10224

lemma sg24265 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9030

lemma sg24266 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10628

lemma sg24267 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg8449 sg10190

lemma sg24268 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8722 sg9482

lemma sg24269 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10123

lemma sg24270 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9758

lemma sg24271 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9487

lemma sg24272 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8809 sg9170

lemma sg24273 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10225

lemma sg24274 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9031

lemma sg24275 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8730 sg9462

lemma sg24276 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8352 sg10626

lemma sg24277 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9488

lemma sg24278 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10226

lemma sg24279 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9032

lemma sg24280 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg8996

lemma sg24281 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9463

lemma sg24282 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg8997

lemma sg24283 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg8450 sg10190

lemma sg24284 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8526 sg10104

lemma sg24285 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8365 sg10606

lemma sg24286 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9033

lemma sg24287 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10094

lemma sg24288 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg8998

lemma sg24289 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg8451 sg10190

lemma sg24290 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg8117 sg11052

lemma sg24291 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg8431 sg10222

lemma sg24292 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg8551 sg10086

lemma sg24293 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15512

lemma sg24294 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14500

lemma sg24295 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2870 sg14849

lemma sg24296 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5548 sg12618

lemma sg24297 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4621 sg12946

lemma sg24298 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8244 sg10845

lemma sg24299 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9189

lemma sg24300 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9459

lemma sg24301 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2871 sg14849

lemma sg24302 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5549 sg12618

lemma sg24303 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5967 sg11829

lemma sg24304 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8577 sg10081

lemma sg24305 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9194

lemma sg24306 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9717

lemma sg24307 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9459

lemma sg24308 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5968 sg11829

lemma sg24309 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10227

lemma sg24310 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9191

lemma sg24311 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10699

lemma sg24312 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9484

lemma sg24313 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9192

lemma sg24314 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9759

lemma sg24315 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10124

lemma sg24316 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9759

lemma sg24317 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8655 sg9674

lemma sg24318 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8823 sg9161

lemma sg24319 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9034

lemma sg24320 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5550 sg12618

lemma sg24321 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5969 sg11829

lemma sg24322 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10228

lemma sg24323 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9195

lemma sg24324 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10700

lemma sg24325 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8722 sg9484

lemma sg24326 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10229

lemma sg24327 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9196

lemma sg24328 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9760

lemma sg24329 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10125

lemma sg24330 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9760

lemma sg24331 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9720

lemma sg24332 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9489

lemma sg24333 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8809 sg9171

lemma sg24334 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8374 sg10601

lemma sg24335 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9035

lemma sg24336 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10600

lemma sg24337 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9724

lemma sg24338 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9485

lemma sg24339 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8813 sg9169

lemma sg24340 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9490

lemma sg24341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10227

lemma sg24342 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9036

lemma sg24343 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10631

lemma sg24344 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10224

lemma sg24345 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10632

lemma sg24346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,4,4,4,3] := by
  exact rowSquare_join (by decide) sg8655 sg9676

lemma sg24347 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5971 sg11828

lemma sg24348 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10230

lemma sg24349 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9197

lemma sg24350 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9761

lemma sg24351 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10126

lemma sg24352 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9761

lemma sg24353 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8444 sg10195

lemma sg24354 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9725

lemma sg24355 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9487

lemma sg24356 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8813 sg9170

lemma sg24357 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9491

lemma sg24358 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10228

lemma sg24359 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9037

lemma sg24360 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10633

lemma sg24361 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9726

lemma sg24362 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9492

lemma sg24363 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10229

lemma sg24364 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9038

lemma sg24365 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10226

lemma sg24366 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10634

lemma sg24367 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,4,3,3] := by
  exact rowSquare_join (by decide) sg8449 sg10192

lemma sg24368 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10224

lemma sg24369 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,4,4,2] := by
  exact rowSquare_join (by decide) sg8655 sg9678

lemma sg24370 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8527 sg10104

lemma sg24371 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10098

lemma sg24372 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg8536 sg10098

lemma sg24373 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg8863 sg8998

lemma sg24374 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,5,3,2] := by
  exact rowSquare_join (by decide) sg8431 sg10223

lemma sg24375 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,5,5,4,1] := by
  exact rowSquare_join (by decide) sg8431 sg10224

lemma sg24376 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8582 sg10080

lemma sg24377 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10082

lemma sg24378 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8729 sg9468

lemma sg24379 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9487

lemma sg24380 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8814 sg9170

lemma sg24381 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9727

lemma sg24382 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9493

lemma sg24383 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10230

lemma sg24384 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9039

lemma sg24385 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9468

lemma sg24386 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9002

lemma sg24387 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,3,3,3] := by
  exact rowSquare_join (by decide) sg5550 sg12619

lemma sg24388 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8445 sg10195

lemma sg24389 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8446 sg10195

lemma sg24390 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8447 sg10195

lemma sg24391 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10226

lemma sg24392 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,4,3,2] := by
  exact rowSquare_join (by decide) sg8431 sg10225

lemma sg24393 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,4,4,1] := by
  exact rowSquare_join (by decide) sg8656 sg9678

lemma sg24394 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg333 sg21316

lemma sg24395 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg8352 sg10634

lemma sg24396 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,5,2,2] := by
  exact rowSquare_join (by decide) sg8451 sg10192

lemma sg24397 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,5,3,1] := by
  exact rowSquare_join (by decide) sg8431 sg10226

lemma sg24398 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,6,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg142 sg21621

lemma sg24399 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14500

lemma sg24400 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2694 sg15004

lemma sg24401 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5551 sg12618

lemma sg24402 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14501

lemma sg24403 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7254 sg11431

lemma sg24404 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9194

lemma sg24405 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7786 sg11247

lemma sg24406 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8505 sg10167

lemma sg24407 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5552 sg12618

lemma sg24408 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5970 sg11829

lemma sg24409 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8579 sg10081

lemma sg24410 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9195

lemma sg24411 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8349 sg10635

lemma sg24412 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8537 sg10095

lemma sg24413 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8580 sg10081

lemma sg24414 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9196

lemma sg24415 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8732 sg9464

lemma sg24416 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10127

lemma sg24417 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8538 sg10095

lemma sg24418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8732 sg9465

lemma sg24419 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8760 sg9443

lemma sg24420 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8539 sg10095

lemma sg24421 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg7794 sg11243

lemma sg24422 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8350 sg10635

lemma sg24423 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5971 sg11829

lemma sg24424 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8581 sg10081

lemma sg24425 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9197

lemma sg24426 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9723

lemma sg24427 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10128

lemma sg24428 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8540 sg10095

lemma sg24429 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8379 sg10600

lemma sg24430 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9724

lemma sg24431 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9489

lemma sg24432 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8813 sg9171

lemma sg24433 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8733 sg9465

lemma sg24434 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8672 sg9660

lemma sg24435 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8351 sg10635

lemma sg24436 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10636

lemma sg24437 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8761 sg9442

lemma sg24438 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9490

lemma sg24439 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8734 sg9464

lemma sg24440 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8352 sg10635

lemma sg24441 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10227

lemma sg24442 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10637

lemma sg24443 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8655 sg9679

lemma sg24444 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8448 sg10193

lemma sg24445 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8449 sg10193

lemma sg24446 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8582 sg10081

lemma sg24447 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10083

lemma sg24448 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9725

lemma sg24449 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9489

lemma sg24450 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8814 sg9171

lemma sg24451 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9726

lemma sg24452 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9491

lemma sg24453 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8734 sg9466

lemma sg24454 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8363 sg10610

lemma sg24455 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10228

lemma sg24456 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10638

lemma sg24457 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,3,3,3] := by
  exact rowSquare_join (by decide) sg8655 sg9680

lemma sg24458 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9492

lemma sg24459 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10229

lemma sg24460 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10639

lemma sg24461 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10227

lemma sg24462 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,3,2] := by
  exact rowSquare_join (by decide) sg8655 sg9681

lemma sg24463 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,4,4,1] := by
  exact rowSquare_join (by decide) sg8450 sg10193

lemma sg24464 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8538 sg10098

lemma sg24465 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg8539 sg10098

lemma sg24466 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,5,5,2,2] := by
  exact rowSquare_join (by decide) sg7246 sg11439

lemma sg24467 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8385 sg10599

lemma sg24468 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9727

lemma sg24469 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9491

lemma sg24470 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8735 sg9466

lemma sg24471 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8841 sg9158

lemma sg24472 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9493

lemma sg24473 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10230

lemma sg24474 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10640

lemma sg24475 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10228

lemma sg24476 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,3,3,2] := by
  exact rowSquare_join (by decide) sg8655 sg9682

lemma sg24477 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10229

lemma sg24478 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10229

lemma sg24479 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,4,2,2] := by
  exact rowSquare_join (by decide) sg8449 sg10195

lemma sg24480 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg8352 sg10639

lemma sg24481 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8762 sg9444

lemma sg24482 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9493

lemma sg24483 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8735 sg9468

lemma sg24484 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,7,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8882 sg8982

lemma sg24485 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,7,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10230

lemma sg24486 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,7,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10230

lemma sg24487 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,7,3,2,2] := by
  exact rowSquare_join (by decide) sg7247 sg11439

lemma sg24488 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,7,7,7,7,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8352 sg10640

lemma sg24489 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,3,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8506 sg10167

lemma sg24490 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10308

lemma sg24491 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8485 sg10169

lemma sg24492 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg7232 sg11454

lemma sg24493 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8422 sg10231

lemma sg24494 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10309

lemma sg24495 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg7232 sg11455

lemma sg24496 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8736 sg9450

lemma sg24497 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8650 sg9729

lemma sg24498 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8455 sg10184

lemma sg24499 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg7232 sg11456

lemma sg24500 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10310

lemma sg24501 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8422 sg10232

lemma sg24502 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8658 sg9662

lemma sg24503 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10232

lemma sg24504 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9730

lemma sg24505 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8659 sg9662

lemma sg24506 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,4,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg8457 sg10184

lemma sg24507 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8486 sg10169

lemma sg24508 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg7232 sg11457

lemma sg24509 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9732

lemma sg24510 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10311

lemma sg24511 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg7232 sg11458

lemma sg24512 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9495

lemma sg24513 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10312

lemma sg24514 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8817 sg9162

lemma sg24515 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8347 sg10643

lemma sg24516 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8736 sg9452

lemma sg24517 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10313

lemma sg24518 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9734

lemma sg24519 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8661 sg9662

lemma sg24520 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10234

lemma sg24521 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9497

lemma sg24522 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8658 sg9665

lemma sg24523 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9735

lemma sg24524 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10235

lemma sg24525 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9041

lemma sg24526 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8662 sg9662

lemma sg24527 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8860 sg9042

lemma sg24528 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9450

lemma sg24529 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8650 sg9736

lemma sg24530 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9162

lemma sg24531 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg7232 sg11459

lemma sg24532 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9495

lemma sg24533 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10314

lemma sg24534 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8422 sg10236

lemma sg24535 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8663 sg9662

lemma sg24536 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10236

lemma sg24537 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8721 sg9496

lemma sg24538 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9497

lemma sg24539 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,5,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8658 sg9668

end UniversalTensorSquare
end
end

end OAI
