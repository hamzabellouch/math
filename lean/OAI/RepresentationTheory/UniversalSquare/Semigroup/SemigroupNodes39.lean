import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37

namespace OAI

/-! Semigroup Nodes 39. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16140 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2137 sg5786

lemma sg16141 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3411 sg4395

lemma sg16142 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg3411 sg4397

lemma sg16143 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg3562 sg4321

lemma sg16144 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3569 sg4316

lemma sg16145 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3302 sg4520

lemma sg16146 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3618 sg4214

lemma sg16147 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3570 sg4316

lemma sg16148 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3620 sg4215

lemma sg16149 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1682 sg6517

lemma sg16150 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg6513

lemma sg16151 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,3] := by
  exact rowSquare_join (by decide) sg1688 sg6514

lemma sg16152 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4226

lemma sg16153 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3501 sg4361

lemma sg16154 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg4885

lemma sg16155 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg3565 sg4320

lemma sg16156 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,3] := by
  exact rowSquare_join (by decide) sg3690 sg4119

lemma sg16157 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg3622 sg4216

lemma sg16158 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg3690 sg4120

lemma sg16159 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3691 sg4120

lemma sg16160 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2150 sg5776

lemma sg16161 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2655 sg4965

lemma sg16162 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2649 sg4966

lemma sg16163 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2653 sg4966

lemma sg16164 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4121

lemma sg16165 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2654 sg4966

lemma sg16166 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg3567 sg4321

lemma sg16167 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3502 sg4361

lemma sg16168 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3691 sg4121

lemma sg16169 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2280 sg5752

lemma sg16170 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3503 sg4360

lemma sg16171 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg3617 sg4218

lemma sg16172 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3504 sg4360

lemma sg16173 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3688 sg4122

lemma sg16174 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3502 sg4362

lemma sg16175 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3502 sg4364

lemma sg16176 : RowSquare [5,5,4,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3695 sg4122

lemma sg16177 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [7,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg3303 sg4359

lemma sg16178 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [8,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3 sg14644

lemma sg16179 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [8,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg3 sg14645

lemma sg16180 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [8,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3250 sg4446

lemma sg16181 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [8,6,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3304 sg4363

lemma sg16182 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg3305 sg4363

lemma sg16183 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg3306 sg4360

lemma sg16184 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [9,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3 sg14646

lemma sg16185 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg3305 sg4365

lemma sg16186 : RowSquare [5,5,5,4,3,2,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg3306 sg4363

lemma sg16187 : RowSquare [6,4,4,3,2,2,2,2,2,2,1,1] [5,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1869 sg6389

lemma sg16188 : RowSquare [6,4,4,3,2,2,2,2,2,2,1,1] [5,5,5,5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1868 sg6390

lemma sg16189 : RowSquare [6,4,4,3,2,2,2,2,2,2,1,1] [6,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1870 sg6389

lemma sg16190 : RowSquare [6,4,4,3,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1871 sg6389

lemma sg16191 : RowSquare [6,4,4,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3362 sg4434

lemma sg16192 : RowSquare [6,4,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3331 sg4501

lemma sg16193 : RowSquare [6,4,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3322 sg4502

lemma sg16194 : RowSquare [6,4,4,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg32 sg12723

lemma sg16195 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [4,4,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2248 sg5672

lemma sg16196 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [5,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1852 sg6457

lemma sg16197 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [5,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2247 sg5673

lemma sg16198 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg6457

lemma sg16199 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1855 sg6457

lemma sg16200 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [5,5,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1850 sg6458

lemma sg16201 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [5,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1857 sg6457

lemma sg16202 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [6,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1859 sg6457

lemma sg16203 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1860 sg6457

lemma sg16204 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [6,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1861 sg6457

lemma sg16205 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1862 sg6457

lemma sg16206 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1863 sg6457

lemma sg16207 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg6458

lemma sg16208 : RowSquare [6,5,3,3,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1867 sg6457

lemma sg16209 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3321 sg4489

lemma sg16210 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1682 sg6511

lemma sg16211 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2630 sg4969

lemma sg16212 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1682 sg6512

lemma sg16213 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2631 sg4969

lemma sg16214 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg8006

lemma sg16215 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2633 sg4969

lemma sg16216 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2648 sg4941

lemma sg16217 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3359 sg4434

lemma sg16218 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3323 sg4489

lemma sg16219 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1758 sg6500

lemma sg16220 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15484

lemma sg16221 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15485

lemma sg16222 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2646 sg4946

lemma sg16223 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3326 sg4488

lemma sg16224 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg3327 sg4488

lemma sg16225 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg3325 sg4491

lemma sg16226 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg3327 sg4489

lemma sg16227 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg2647 sg4949

lemma sg16228 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14554

lemma sg16229 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3616 sg4191

lemma sg16230 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3553 sg4319

lemma sg16231 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg4970

lemma sg16232 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg3329 sg4488

lemma sg16233 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3359 sg4435

lemma sg16234 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg3687 sg4111

lemma sg16235 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg2633 sg4971

lemma sg16236 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg3329 sg4489

lemma sg16237 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg1688 sg6509

lemma sg16238 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1775 sg6492

lemma sg16239 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3322 sg4494

lemma sg16240 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3321 sg4495

lemma sg16241 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14555

lemma sg16242 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3333 sg4486

lemma sg16243 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2140 sg5777

lemma sg16244 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg4972

lemma sg16245 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3332 sg4487

lemma sg16246 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1686 sg6510

lemma sg16247 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg14556

lemma sg16248 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13509

lemma sg16249 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13510

lemma sg16250 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13511

lemma sg16251 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,4] := by
  exact rowSquare_join (by decide) sg3332 sg4488

lemma sg16252 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14557

lemma sg16253 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14558

lemma sg16254 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,3] := by
  exact rowSquare_join (by decide) sg3358 sg4438

lemma sg16255 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3322 sg4496

lemma sg16256 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3324 sg4496

lemma sg16257 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3325 sg4496

lemma sg16258 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg4881

lemma sg16259 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3555 sg4319

lemma sg16260 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg2633 sg4973

lemma sg16261 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3,1] := by
  exact rowSquare_join (by decide) sg3333 sg4488

lemma sg16262 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13512

lemma sg16263 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13513

lemma sg16264 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,4,3] := by
  exact rowSquare_join (by decide) sg3410 sg4378

lemma sg16265 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13514

lemma sg16266 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg3690 sg4111

lemma sg16267 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3732 sg4031

lemma sg16268 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15486

lemma sg16269 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15487

lemma sg16270 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3403 sg4404

lemma sg16271 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14559

lemma sg16272 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14560

lemma sg16273 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg15488

lemma sg16274 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14821

lemma sg16275 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14822

lemma sg16276 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg1 sg14823

lemma sg16277 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,4] := by
  exact rowSquare_join (by decide) sg2651 sg4949

lemma sg16278 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14553

lemma sg16279 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg5 sg14554

lemma sg16280 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg4 sg14562

lemma sg16281 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg4 sg14563

lemma sg16282 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15489

lemma sg16283 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13515

lemma sg16284 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13516

lemma sg16285 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15490

lemma sg16286 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg5 sg14558

lemma sg16287 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg0 sg15491

lemma sg16288 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14564

lemma sg16289 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14565

lemma sg16290 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14566

lemma sg16291 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14567

lemma sg16292 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14568

lemma sg16293 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15492

lemma sg16294 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14569

lemma sg16295 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14570

lemma sg16296 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14571

lemma sg16297 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13518

lemma sg16298 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13519

lemma sg16299 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13520

lemma sg16300 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13521

lemma sg16301 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13522

lemma sg16302 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13523

lemma sg16303 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14572

lemma sg16304 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,2] := by
  exact rowSquare_join (by decide) sg4 sg14573

lemma sg16305 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15493

lemma sg16306 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15494

lemma sg16307 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg3403 sg4405

lemma sg16308 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13524

lemma sg16309 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13525

lemma sg16310 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15495

lemma sg16311 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13526

lemma sg16312 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg13 sg13527

lemma sg16313 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg39 sg12723

lemma sg16314 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg0 sg15496

lemma sg16315 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3335 sg4485

lemma sg16316 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2633 sg4974

lemma sg16317 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg3687 sg4112

lemma sg16318 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg3617 sg4195

lemma sg16319 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3329 sg4492

lemma sg16320 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14574

lemma sg16321 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13510

lemma sg16322 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13511

lemma sg16323 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,4] := by
  exact rowSquare_join (by decide) sg3332 sg4492

lemma sg16324 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3322 sg4497

lemma sg16325 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4209

lemma sg16326 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4114

lemma sg16327 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13529

lemma sg16328 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13530

lemma sg16329 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13531

lemma sg16330 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13532

lemma sg16331 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13533

lemma sg16332 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13534

lemma sg16333 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13514

lemma sg16334 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg3733 sg4031

lemma sg16335 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14575

lemma sg16336 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13535

lemma sg16337 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13536

lemma sg16338 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14576

lemma sg16339 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg14577

lemma sg16340 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg14578

lemma sg16341 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13537

lemma sg16342 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13538

lemma sg16343 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13539

lemma sg16344 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13540

lemma sg16345 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13541

lemma sg16346 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg13 sg13542

lemma sg16347 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg40 sg12723

lemma sg16348 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3328 sg4496

lemma sg16349 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13543

lemma sg16350 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13544

lemma sg16351 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13545

lemma sg16352 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13546

lemma sg16353 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13547

lemma sg16354 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg13548

lemma sg16355 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3336 sg4486

lemma sg16356 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3688 sg4115

lemma sg16357 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1775 sg6493

lemma sg16358 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4212

lemma sg16359 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13549

lemma sg16360 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14579

lemma sg16361 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14580

lemma sg16362 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14581

lemma sg16363 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13550

lemma sg16364 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13551

lemma sg16365 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13552

lemma sg16366 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13553

lemma sg16367 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13554

lemma sg16368 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14582

lemma sg16369 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14583

lemma sg16370 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14584

lemma sg16371 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13555

lemma sg16372 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13556

lemma sg16373 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13557

lemma sg16374 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13558

lemma sg16375 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13559

lemma sg16376 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg4 sg14585

lemma sg16377 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3331 sg4496

lemma sg16378 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13560

lemma sg16379 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13561

lemma sg16380 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13562

lemma sg16381 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,6,4] := by
  exact rowSquare_join (by decide) sg13 sg13563

lemma sg16382 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg3333 sg4496

lemma sg16383 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13564

lemma sg16384 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,3] := by
  exact rowSquare_join (by decide) sg13 sg13565

lemma sg16385 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3403 sg4406

lemma sg16386 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14824

lemma sg16387 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14559

lemma sg16388 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg5 sg14560

lemma sg16389 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14825

lemma sg16390 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14586

lemma sg16391 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg4 sg14587

lemma sg16392 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg4 sg14588

lemma sg16393 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg6 sg14556

lemma sg16394 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13566

lemma sg16395 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13567

lemma sg16396 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13568

lemma sg16397 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15497

lemma sg16398 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg6 sg14558

lemma sg16399 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1 sg14826

lemma sg16400 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14827

lemma sg16401 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14561

lemma sg16402 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg5 sg14562

lemma sg16403 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg5 sg14563

lemma sg16404 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14828

lemma sg16405 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14589

lemma sg16406 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13569

lemma sg16407 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14590

lemma sg16408 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14591

lemma sg16409 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14592

lemma sg16410 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13570

lemma sg16411 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13571

lemma sg16412 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13572

lemma sg16413 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13573

lemma sg16414 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13574

lemma sg16415 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg5 sg14572

lemma sg16416 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,2] := by
  exact rowSquare_join (by decide) sg5 sg14573

lemma sg16417 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,3,2] := by
  exact rowSquare_join (by decide) sg4 sg14593

lemma sg16418 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13575

lemma sg16419 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13576

lemma sg16420 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13577

lemma sg16421 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,4,3] := by
  exact rowSquare_join (by decide) sg4 sg14594

lemma sg16422 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13578

lemma sg16423 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13579

lemma sg16424 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13580

lemma sg16425 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12724

lemma sg16426 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,2] := by
  exact rowSquare_join (by decide) sg39 sg12725

lemma sg16427 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg41 sg12723

lemma sg16428 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13581

lemma sg16429 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13582

lemma sg16430 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13583

lemma sg16431 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13584

lemma sg16432 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg39 sg12726

lemma sg16433 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,5] := by
  exact rowSquare_join (by decide) sg39 sg12727

lemma sg16434 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15498

lemma sg16435 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15499

lemma sg16436 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14595

lemma sg16437 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13585

lemma sg16438 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15500

lemma sg16439 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13515

lemma sg16440 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13516

lemma sg16441 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15501

lemma sg16442 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13517

lemma sg16443 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13586

lemma sg16444 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13587

lemma sg16445 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg14 sg13522

lemma sg16446 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg13523

lemma sg16447 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13588

lemma sg16448 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13589

lemma sg16449 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13590

lemma sg16450 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13591

lemma sg16451 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13592

lemma sg16452 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg39 sg12728

lemma sg16453 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,5,1] := by
  exact rowSquare_join (by decide) sg42 sg12723

lemma sg16454 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14596

lemma sg16455 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg14597

lemma sg16456 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13593

lemma sg16457 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13594

lemma sg16458 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12724

lemma sg16459 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg40 sg12725

lemma sg16460 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13595

lemma sg16461 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12729

lemma sg16462 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,2] := by
  exact rowSquare_join (by decide) sg39 sg12730

lemma sg16463 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,4,1] := by
  exact rowSquare_join (by decide) sg39 sg12731

lemma sg16464 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,5] := by
  exact rowSquare_join (by decide) sg40 sg12727

lemma sg16465 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13596

lemma sg16466 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13597

lemma sg16467 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,3,1] := by
  exact rowSquare_join (by decide) sg39 sg12732

lemma sg16468 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg39 sg12733

lemma sg16469 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,7,6,3] := by
  exact rowSquare_join (by decide) sg39 sg12734

lemma sg16470 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,7,7,7,2] := by
  exact rowSquare_join (by decide) sg39 sg12735

lemma sg16471 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3320 sg4498

lemma sg16472 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3558 sg4323

lemma sg16473 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3320 sg4499

lemma sg16474 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3322 sg4498

lemma sg16475 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3626 sg4195

lemma sg16476 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3687 sg4116

lemma sg16477 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4213

lemma sg16478 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2633 sg4975

lemma sg16479 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg14 sg13528

lemma sg16480 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg4118

lemma sg16481 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13600

lemma sg16482 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13601

lemma sg16483 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13532

lemma sg16484 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg13534

lemma sg16485 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg13535

lemma sg16486 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg13536

lemma sg16487 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13602

lemma sg16488 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg13603

lemma sg16489 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg14 sg13541

lemma sg16490 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,4,4,2] := by
  exact rowSquare_join (by decide) sg40 sg12728

lemma sg16491 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13604

lemma sg16492 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13605

lemma sg16493 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13606

lemma sg16494 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg13607

lemma sg16495 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,5,5] := by
  exact rowSquare_join (by decide) sg14 sg13548

lemma sg16496 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13608

lemma sg16497 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg13554

lemma sg16498 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13609

lemma sg16499 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12729

lemma sg16500 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,3,2] := by
  exact rowSquare_join (by decide) sg40 sg12730

lemma sg16501 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,4,4,1] := by
  exact rowSquare_join (by decide) sg40 sg12731

lemma sg16502 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13610

lemma sg16503 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13611

lemma sg16504 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,3,1] := by
  exact rowSquare_join (by decide) sg40 sg12732

lemma sg16505 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,5,4] := by
  exact rowSquare_join (by decide) sg40 sg12733

lemma sg16506 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13612

lemma sg16507 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,2,1] := by
  exact rowSquare_join (by decide) sg13 sg13613

lemma sg16508 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,6,6,3] := by
  exact rowSquare_join (by decide) sg13 sg13614

lemma sg16509 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,7,5,3] := by
  exact rowSquare_join (by decide) sg40 sg12734

lemma sg16510 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,7,6,2] := by
  exact rowSquare_join (by decide) sg40 sg12735

lemma sg16511 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,7,7,1] := by
  exact rowSquare_join (by decide) sg13 sg13615

lemma sg16512 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,8,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13616

lemma sg16513 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,8,5,2] := by
  exact rowSquare_join (by decide) sg13 sg13617

lemma sg16514 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,8,6,1] := by
  exact rowSquare_join (by decide) sg13 sg13618

lemma sg16515 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [8,8,8,7] := by
  exact rowSquare_join (by decide) sg13 sg13619

lemma sg16516 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14829

lemma sg16517 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14830

lemma sg16518 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14831

lemma sg16519 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6 sg14559

lemma sg16520 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg6 sg14560

lemma sg16521 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14832

lemma sg16522 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14833

lemma sg16523 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg14586

lemma sg16524 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg5 sg14588

lemma sg16525 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg14834

lemma sg16526 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14598

lemma sg16527 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg4 sg14599

lemma sg16528 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13620

lemma sg16529 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg13621

lemma sg16530 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14600

lemma sg16531 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg15 sg13510

lemma sg16532 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14601

lemma sg16533 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13622

lemma sg16534 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg13623

lemma sg16535 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg13624

lemma sg16536 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg13625

lemma sg16537 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg13 sg13626

lemma sg16538 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg15 sg13514

lemma sg16539 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg6 sg14573

end UniversalTensorSquare
end
end

end OAI
