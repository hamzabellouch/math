import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 64. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg26140 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9226

lemma sg26141 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9808

lemma sg26142 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9554

lemma sg26143 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10283

lemma sg26144 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9109

lemma sg26145 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10279

lemma sg26146 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10675

lemma sg26147 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9551

lemma sg26148 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10280

lemma sg26149 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10676

lemma sg26150 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10278

lemma sg26151 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8538 sg10104

lemma sg26152 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9260

lemma sg26153 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9809

lemma sg26154 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9555

lemma sg26155 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10284

lemma sg26156 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9110

lemma sg26157 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8730 sg9493

lemma sg26158 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9493

lemma sg26159 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9039

lemma sg26160 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10280

lemma sg26161 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14508

lemma sg26162 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5565 sg12618

lemma sg26163 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5992 sg11829

lemma sg26164 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10384

lemma sg26165 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9256

lemma sg26166 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9194

lemma sg26167 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10384

lemma sg26168 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5993 sg11829

lemma sg26169 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9227

lemma sg26170 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9257

lemma sg26171 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9805

lemma sg26172 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10136

lemma sg26173 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8568 sg10095

lemma sg26174 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9227

lemma sg26175 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9227

lemma sg26176 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9227

lemma sg26177 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9227

lemma sg26178 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8756 sg9465

lemma sg26179 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8569 sg10095

lemma sg26180 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8863 sg9034

lemma sg26181 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10677

lemma sg26182 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9228

lemma sg26183 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9228

lemma sg26184 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9228

lemma sg26185 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9228

lemma sg26186 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9228

lemma sg26187 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9807

lemma sg26188 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9552

lemma sg26189 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8813 sg9195

lemma sg26190 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8363 sg10635

lemma sg26191 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10281

lemma sg26192 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10678

lemma sg26193 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9553

lemma sg26194 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10282

lemma sg26195 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10679

lemma sg26196 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9260

lemma sg26197 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9808

lemma sg26198 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9552

lemma sg26199 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8814 sg9195

lemma sg26200 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8881 sg8999

lemma sg26201 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9554

lemma sg26202 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10283

lemma sg26203 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10680

lemma sg26204 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10282

lemma sg26205 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9809

lemma sg26206 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9555

lemma sg26207 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10284

lemma sg26208 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10681

lemma sg26209 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10283

lemma sg26210 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9555

lemma sg26211 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,7,7,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10284

lemma sg26212 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,3,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10385

lemma sg26213 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10308

lemma sg26214 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10386

lemma sg26215 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9811

lemma sg26216 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10387

lemma sg26217 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9846

lemma sg26218 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8727 sg9495

lemma sg26219 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10388

lemma sg26220 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10309

lemma sg26221 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8419 sg10309

lemma sg26222 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8736 sg9475

lemma sg26223 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10389

lemma sg26224 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10137

lemma sg26225 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9847

lemma sg26226 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10287

lemma sg26227 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10310

lemma sg26228 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8419 sg10310

lemma sg26229 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9814

lemma sg26230 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10288

lemma sg26231 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8861 sg9041

lemma sg26232 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9498

lemma sg26233 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,4,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8861 sg9042

lemma sg26234 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9815

lemma sg26235 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10390

lemma sg26236 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9848

lemma sg26237 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9557

lemma sg26238 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10391

lemma sg26239 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10311

lemma sg26240 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9849

lemma sg26241 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9495

lemma sg26242 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10392

lemma sg26243 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10312

lemma sg26244 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9850

lemma sg26245 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10291

lemma sg26246 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10393

lemma sg26247 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10313

lemma sg26248 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9851

lemma sg26249 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9818

lemma sg26250 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10292

lemma sg26251 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9111

lemma sg26252 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9819

lemma sg26253 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10293

lemma sg26254 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10288

lemma sg26255 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9112

lemma sg26256 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8862 sg9042

lemma sg26257 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9557

lemma sg26258 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10394

lemma sg26259 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10138

lemma sg26260 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9852

lemma sg26261 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10294

lemma sg26262 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9557

lemma sg26263 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10395

lemma sg26264 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10314

lemma sg26265 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9853

lemma sg26266 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9821

lemma sg26267 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10295

lemma sg26268 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8861 sg9046

lemma sg26269 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10139

lemma sg26270 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9854

lemma sg26271 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9822

lemma sg26272 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10296

lemma sg26273 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9205

lemma sg26274 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8861 sg9047

lemma sg26275 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9206

lemma sg26276 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9206

lemma sg26277 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9048

lemma sg26278 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10683

lemma sg26279 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10396

lemma sg26280 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10315

lemma sg26281 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9855

lemma sg26282 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9823

lemma sg26283 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10297

lemma sg26284 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9506

lemma sg26285 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8861 sg9049

lemma sg26286 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9824

lemma sg26287 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10298

lemma sg26288 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9507

lemma sg26289 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9507

lemma sg26290 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9050

lemma sg26291 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8659 sg9711

lemma sg26292 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9712

lemma sg26293 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8659 sg9712

lemma sg26294 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8531 sg10108

lemma sg26295 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10108

lemma sg26296 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9051

lemma sg26297 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8179 sg10860

lemma sg26298 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,5,5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg8543 sg10102

lemma sg26299 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1319 sg20964

lemma sg26300 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1722 sg18244

lemma sg26301 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1825 sg17111

lemma sg26302 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2191 sg15564

lemma sg26303 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15534

lemma sg26304 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2677 sg15014

lemma sg26305 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg15574

lemma sg26306 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14681

lemma sg26307 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg867 sg21145

lemma sg26308 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg867 sg21146

lemma sg26309 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg867 sg21147

lemma sg26310 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1826 sg17111

lemma sg26311 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2192 sg15564

lemma sg26312 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2225 sg15534

lemma sg26313 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2670 sg15018

lemma sg26314 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2867 sg14855

lemma sg26315 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5539 sg12628

lemma sg26316 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14682

lemma sg26317 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10289

lemma sg26318 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8369 sg10620

lemma sg26319 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2226 sg15534

lemma sg26320 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3871 sg14510

lemma sg26321 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15535

lemma sg26322 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6944 sg11469

lemma sg26323 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5587 sg12611

lemma sg26324 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9200

lemma sg26325 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8544 sg10101

lemma sg26326 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8729 sg9499

lemma sg26327 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2669 sg15020

lemma sg26328 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6945 sg11469

lemma sg26329 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5961 sg11834

lemma sg26330 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9201

lemma sg26331 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9182

lemma sg26332 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8651 sg9815

lemma sg26333 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6563 sg11541

lemma sg26334 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10397

lemma sg26335 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9183

lemma sg26336 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9825

lemma sg26337 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9558

lemma sg26338 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9184

lemma sg26339 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10716

lemma sg26340 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10397

lemma sg26341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10140

lemma sg26342 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9856

lemma sg26343 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2193 sg15564

lemma sg26344 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2227 sg15534

lemma sg26345 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3872 sg14510

lemma sg26346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14854

lemma sg26347 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6946 sg11469

lemma sg26348 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5539 sg12629

lemma sg26349 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10290

lemma sg26350 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8444 sg10233

lemma sg26351 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8732 sg9499

lemma sg26352 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14509

lemma sg26353 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2671 sg15019

lemma sg26354 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6949 sg11468

lemma sg26355 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5963 sg11834

lemma sg26356 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10291

lemma sg26357 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9264

lemma sg26358 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8652 sg9815

lemma sg26359 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6947 sg11469

lemma sg26360 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6564 sg11541

lemma sg26361 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10316

lemma sg26362 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9201

lemma sg26363 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9816

lemma sg26364 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9558

lemma sg26365 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10398

lemma sg26366 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10316

lemma sg26367 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10717

lemma sg26368 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10398

lemma sg26369 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9857

lemma sg26370 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10316

lemma sg26371 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9857

lemma sg26372 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8347 sg10691

lemma sg26373 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3766 sg14539

lemma sg26374 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6948 sg11469

lemma sg26375 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6565 sg11541

lemma sg26376 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10299

lemma sg26377 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9265

lemma sg26378 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9200

lemma sg26379 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9558

lemma sg26380 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5995 sg11828

lemma sg26381 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10399

lemma sg26382 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9266

lemma sg26383 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10718

lemma sg26384 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10399

lemma sg26385 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9267

lemma sg26386 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9858

lemma sg26387 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10141

lemma sg26388 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9858

lemma sg26389 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9827

lemma sg26390 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10299

lemma sg26391 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9113

lemma sg26392 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10317

lemma sg26393 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10317

lemma sg26394 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9859

lemma sg26395 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10317

lemma sg26396 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9859

lemma sg26397 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9828

lemma sg26398 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9828

lemma sg26399 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10300

lemma sg26400 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10292

lemma sg26401 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9114

lemma sg26402 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9559

lemma sg26403 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10293

lemma sg26404 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9115

lemma sg26405 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg9044

lemma sg26406 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15517

lemma sg26407 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14509

lemma sg26408 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2870 sg14854

lemma sg26409 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6950 sg11468

lemma sg26410 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5994 sg11829

lemma sg26411 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10294

lemma sg26412 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9264

lemma sg26413 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9500

lemma sg26414 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3767 sg14539

lemma sg26415 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6951 sg11468

lemma sg26416 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5967 sg11833

lemma sg26417 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10301

lemma sg26418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9268

lemma sg26419 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9816

lemma sg26420 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9500

lemma sg26421 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6566 sg11541

lemma sg26422 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10400

lemma sg26423 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9266

lemma sg26424 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10719

lemma sg26425 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10400

lemma sg26426 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10318

lemma sg26427 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9860

lemma sg26428 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10318

lemma sg26429 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9860

lemma sg26430 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9829

lemma sg26431 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10301

lemma sg26432 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9116

lemma sg26433 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6952 sg11468

lemma sg26434 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6567 sg11541

lemma sg26435 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10401

lemma sg26436 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9269

lemma sg26437 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10720

lemma sg26438 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10401

lemma sg26439 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10319

lemma sg26440 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10319

lemma sg26441 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9861

lemma sg26442 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10319

lemma sg26443 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9861

lemma sg26444 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9830

lemma sg26445 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9830

lemma sg26446 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10302

lemma sg26447 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10295

lemma sg26448 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9117

lemma sg26449 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10618

lemma sg26450 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9831

lemma sg26451 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9831

lemma sg26452 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10303

lemma sg26453 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9560

lemma sg26454 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10296

lemma sg26455 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9118

lemma sg26456 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10684

lemma sg26457 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10293

lemma sg26458 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10685

lemma sg26459 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6568 sg11541

lemma sg26460 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10304

lemma sg26461 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9271

lemma sg26462 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9862

lemma sg26463 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10142

lemma sg26464 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9862

lemma sg26465 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10242

lemma sg26466 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9832

lemma sg26467 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9832

lemma sg26468 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10304

lemma sg26469 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9561

lemma sg26470 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10297

lemma sg26471 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9119

lemma sg26472 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg9049

lemma sg26473 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9824

lemma sg26474 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9562

lemma sg26475 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10298

lemma sg26476 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9120

lemma sg26477 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9507

lemma sg26478 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9050

lemma sg26479 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8534 sg10108

lemma sg26480 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10108

lemma sg26481 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9051

lemma sg26482 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14509

lemma sg26483 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3768 sg14539

lemma sg26484 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6953 sg11468

lemma sg26485 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5996 sg11829

lemma sg26486 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9215

lemma sg26487 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9268

lemma sg26488 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9203

lemma sg26489 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9477

lemma sg26490 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6954 sg11468

lemma sg26491 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5970 sg11833

lemma sg26492 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10402

lemma sg26493 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9215

lemma sg26494 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10721

lemma sg26495 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10402

lemma sg26496 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9217

lemma sg26497 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9270

lemma sg26498 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9863

lemma sg26499 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10143

lemma sg26500 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9863

lemma sg26501 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9833

lemma sg26502 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9833

lemma sg26503 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10305

lemma sg26504 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9215

lemma sg26505 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8861 sg9060

lemma sg26506 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5971 sg11833

lemma sg26507 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10320

lemma sg26508 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10320

lemma sg26509 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9864

lemma sg26510 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10320

lemma sg26511 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9864

lemma sg26512 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9217

lemma sg26513 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9834

lemma sg26514 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9834

lemma sg26515 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10306

lemma sg26516 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9216

lemma sg26517 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9216

lemma sg26518 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9061

lemma sg26519 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10686

lemma sg26520 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9217

lemma sg26521 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9217

lemma sg26522 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9217

lemma sg26523 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9062

lemma sg26524 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10296

lemma sg26525 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10687

lemma sg26526 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10307

lemma sg26527 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9218

lemma sg26528 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9835

lemma sg26529 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9835

lemma sg26530 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10307

lemma sg26531 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9218

lemma sg26532 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9218

lemma sg26533 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9218

lemma sg26534 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9063

lemma sg26535 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10297

lemma sg26536 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10688

lemma sg26537 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9562

lemma sg26538 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10298

lemma sg26539 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,8,6,6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10689

end UniversalTensorSquare
end
end

end OAI
