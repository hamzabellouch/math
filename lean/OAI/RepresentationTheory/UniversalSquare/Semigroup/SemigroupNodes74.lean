import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 74. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg30140 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2192 sg15571

lemma sg30141 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2225 sg15547

lemma sg30142 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3882 sg14510

lemma sg30143 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2867 sg14862

lemma sg30144 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6981 sg11469

lemma sg30145 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5983 sg11834

lemma sg30146 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10361

lemma sg30147 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8369 sg10661

lemma sg30148 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2226 sg15547

lemma sg30149 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3871 sg14517

lemma sg30150 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15548

lemma sg30151 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6944 sg11473

lemma sg30152 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5532 sg12633

lemma sg30153 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10366

lemma sg30154 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10289

lemma sg30155 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8729 sg9556

lemma sg30156 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3870 sg14519

lemma sg30157 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6937 sg11476

lemma sg30158 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6572 sg11541

lemma sg30159 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10390

lemma sg30160 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9297

lemma sg30161 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8651 sg9921

lemma sg30162 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6914 sg11480

lemma sg30163 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10475

lemma sg30164 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10390

lemma sg30165 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9926

lemma sg30166 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9614

lemma sg30167 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9240

lemma sg30168 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10807

lemma sg30169 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10475

lemma sg30170 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10390

lemma sg30171 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9955

lemma sg30172 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2193 sg15571

lemma sg30173 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2227 sg15547

lemma sg30174 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3872 sg14517

lemma sg30175 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14861

lemma sg30176 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6946 sg11473

lemma sg30177 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5534 sg12633

lemma sg30178 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10362

lemma sg30179 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8444 sg10285

lemma sg30180 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8732 sg9556

lemma sg30181 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3886 sg14509

lemma sg30182 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3871 sg14518

lemma sg30183 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6938 sg11476

lemma sg30184 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6944 sg11474

lemma sg30185 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10367

lemma sg30186 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9343

lemma sg30187 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8652 sg9921

lemma sg30188 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6939 sg11476

lemma sg30189 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6915 sg11480

lemma sg30190 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10391

lemma sg30191 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9298

lemma sg30192 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9922

lemma sg30193 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9614

lemma sg30194 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10476

lemma sg30195 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10391

lemma sg30196 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10808

lemma sg30197 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10476

lemma sg30198 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9956

lemma sg30199 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10391

lemma sg30200 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9956

lemma sg30201 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10367

lemma sg30202 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3772 sg14539

lemma sg30203 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6940 sg11476

lemma sg30204 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6916 sg11480

lemma sg30205 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10368

lemma sg30206 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9344

lemma sg30207 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9261

lemma sg30208 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9614

lemma sg30209 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5995 sg11831

lemma sg30210 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10477

lemma sg30211 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9299

lemma sg30212 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10809

lemma sg30213 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10477

lemma sg30214 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10392

lemma sg30215 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9957

lemma sg30216 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10392

lemma sg30217 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9957

lemma sg30218 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9928

lemma sg30219 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10368

lemma sg30220 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10393

lemma sg30221 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10393

lemma sg30222 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9958

lemma sg30223 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10393

lemma sg30224 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9958

lemma sg30225 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9929

lemma sg30226 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9929

lemma sg30227 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10369

lemma sg30228 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10364

lemma sg30229 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9615

lemma sg30230 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10365

lemma sg30231 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15531

lemma sg30232 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3887 sg14509

lemma sg30233 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3872 sg14518

lemma sg30234 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6987 sg11468

lemma sg30235 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6946 sg11474

lemma sg30236 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9268

lemma sg30237 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9343

lemma sg30238 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9557

lemma sg30239 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3769 sg14542

lemma sg30240 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6941 sg11476

lemma sg30241 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5987 sg11833

lemma sg30242 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10370

lemma sg30243 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9268

lemma sg30244 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9922

lemma sg30245 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9557

lemma sg30246 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6917 sg11480

lemma sg30247 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10478

lemma sg30248 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9301

lemma sg30249 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10810

lemma sg30250 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10478

lemma sg30251 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10394

lemma sg30252 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9959

lemma sg30253 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10394

lemma sg30254 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9959

lemma sg30255 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9930

lemma sg30256 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10370

lemma sg30257 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6942 sg11476

lemma sg30258 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6918 sg11480

lemma sg30259 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10479

lemma sg30260 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9269

lemma sg30261 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10811

lemma sg30262 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10479

lemma sg30263 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10395

lemma sg30264 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10395

lemma sg30265 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9960

lemma sg30266 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10395

lemma sg30267 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9960

lemma sg30268 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9931

lemma sg30269 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9931

lemma sg30270 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10371

lemma sg30271 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9269

lemma sg30272 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9303

lemma sg30273 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9932

lemma sg30274 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9932

lemma sg30275 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10372

lemma sg30276 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9270

lemma sg30277 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9270

lemma sg30278 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6919 sg11480

lemma sg30279 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10396

lemma sg30280 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10396

lemma sg30281 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9961

lemma sg30282 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10396

lemma sg30283 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9961

lemma sg30284 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9304

lemma sg30285 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9933

lemma sg30286 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9933

lemma sg30287 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10373

lemma sg30288 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9271

lemma sg30289 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9271

lemma sg30290 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8726 sg9562

lemma sg30291 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9562

lemma sg30292 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9562

lemma sg30293 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8542 sg10130

lemma sg30294 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1723 sg18251

lemma sg30295 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1830 sg17121

lemma sg30296 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2197 sg15569

lemma sg30297 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2234 sg15534

lemma sg30298 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3884 sg14510

lemma sg30299 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2868 sg14862

lemma sg30300 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6984 sg11469

lemma sg30301 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5985 sg11834

lemma sg30302 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8443 sg10289

lemma sg30303 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8383 sg10620

lemma sg30304 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2198 sg15569

lemma sg30305 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2235 sg15534

lemma sg30306 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3885 sg14510

lemma sg30307 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2869 sg14862

lemma sg30308 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6985 sg11469

lemma sg30309 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5539 sg12631

lemma sg30310 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10366

lemma sg30311 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8444 sg10289

lemma sg30312 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8660 sg9784

lemma sg30313 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14517

lemma sg30314 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3871 sg14519

lemma sg30315 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6949 sg11473

lemma sg30316 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6576 sg11541

lemma sg30317 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9305

lemma sg30318 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9345

lemma sg30319 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8729 sg9558

lemma sg30320 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6986 sg11469

lemma sg30321 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6577 sg11541

lemma sg30322 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10397

lemma sg30323 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9305

lemma sg30324 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9926

lemma sg30325 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9558

lemma sg30326 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10480

lemma sg30327 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10397

lemma sg30328 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10812

lemma sg30329 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10480

lemma sg30330 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9962

lemma sg30331 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10397

lemma sg30332 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9962

lemma sg30333 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8347 sg10708

lemma sg30334 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15534

lemma sg30335 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14517

lemma sg30336 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3872 sg14519

lemma sg30337 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6950 sg11473

lemma sg30338 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6578 sg11541

lemma sg30339 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10367

lemma sg30340 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9345

lemma sg30341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9558

lemma sg30342 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3769 sg14543

lemma sg30343 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6951 sg11473

lemma sg30344 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6579 sg11541

lemma sg30345 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10374

lemma sg30346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9346

lemma sg30347 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9926

lemma sg30348 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9558

lemma sg30349 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6580 sg11541

lemma sg30350 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10481

lemma sg30351 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9306

lemma sg30352 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10813

lemma sg30353 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10481

lemma sg30354 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10398

lemma sg30355 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9963

lemma sg30356 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10398

lemma sg30357 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9963

lemma sg30358 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9935

lemma sg30359 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10374

lemma sg30360 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6952 sg11473

lemma sg30361 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6581 sg11541

lemma sg30362 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10482

lemma sg30363 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9347

lemma sg30364 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10814

lemma sg30365 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10482

lemma sg30366 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10399

lemma sg30367 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10399

lemma sg30368 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9964

lemma sg30369 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10399

lemma sg30370 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9964

lemma sg30371 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9936

lemma sg30372 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9936

lemma sg30373 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10375

lemma sg30374 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10368

lemma sg30375 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9307

lemma sg30376 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9937

lemma sg30377 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9937

lemma sg30378 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10376

lemma sg30379 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9616

lemma sg30380 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10369

lemma sg30381 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14517

lemma sg30382 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14518

lemma sg30383 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6953 sg11473

lemma sg30384 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6582 sg11541

lemma sg30385 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10370

lemma sg30386 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9346

lemma sg30387 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9264

lemma sg30388 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9543

lemma sg30389 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6954 sg11473

lemma sg30390 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6583 sg11541

lemma sg30391 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10483

lemma sg30392 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9348

lemma sg30393 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10815

lemma sg30394 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10483

lemma sg30395 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10400

lemma sg30396 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10400

lemma sg30397 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9965

lemma sg30398 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10400

lemma sg30399 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9965

lemma sg30400 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9938

lemma sg30401 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9938

lemma sg30402 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10377

lemma sg30403 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10370

lemma sg30404 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6584 sg11541

lemma sg30405 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10401

lemma sg30406 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10401

lemma sg30407 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9966

lemma sg30408 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10401

lemma sg30409 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9966

lemma sg30410 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9308

lemma sg30411 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9939

lemma sg30412 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9939

lemma sg30413 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10378

lemma sg30414 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9617

lemma sg30415 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10371

lemma sg30416 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9932

lemma sg30417 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9618

lemma sg30418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10372

lemma sg30419 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10379

lemma sg30420 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9309

lemma sg30421 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9940

lemma sg30422 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9940

lemma sg30423 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10379

lemma sg30424 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9933

lemma sg30425 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9619

lemma sg30426 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10373

lemma sg30427 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8730 sg9562

lemma sg30428 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14518

lemma sg30429 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6993 sg11468

lemma sg30430 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6953 sg11474

lemma sg30431 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10484

lemma sg30432 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9348

lemma sg30433 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10816

lemma sg30434 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10484

lemma sg30435 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6954 sg11474

lemma sg30436 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10402

lemma sg30437 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10402

lemma sg30438 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9967

lemma sg30439 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10402

lemma sg30440 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9967

lemma sg30441 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9310

lemma sg30442 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9941

lemma sg30443 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9941

lemma sg30444 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10380

lemma sg30445 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9280

lemma sg30446 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9280

lemma sg30447 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10381

lemma sg30448 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9311

lemma sg30449 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9942

lemma sg30450 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9942

lemma sg30451 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10381

lemma sg30452 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9281

lemma sg30453 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9281

lemma sg30454 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9618

lemma sg30455 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9282

lemma sg30456 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9282

lemma sg30457 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9282

lemma sg30458 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9619

lemma sg30459 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9809

lemma sg30460 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9555

lemma sg30461 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1831 sg17121

lemma sg30462 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2199 sg15569

lemma sg30463 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2240 sg15529

lemma sg30464 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2684 sg15016

lemma sg30465 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2874 sg14855

lemma sg30466 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5261 sg12690

lemma sg30467 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3518 sg14683

lemma sg30468 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9272

lemma sg30469 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5628 sg12604

lemma sg30470 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8666 sg9784

lemma sg30471 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2241 sg15529

lemma sg30472 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3888 sg14510

lemma sg30473 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3771 sg14541

lemma sg30474 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6989 sg11469

lemma sg30475 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5989 sg11834

lemma sg30476 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9283

lemma sg30477 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9272

lemma sg30478 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8660 sg9795

lemma sg30479 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14519

lemma sg30480 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6990 sg11469

lemma sg30481 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6949 sg11475

lemma sg30482 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9312

lemma sg30483 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9351

lemma sg30484 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9272

lemma sg30485 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8737 sg9546

lemma sg30486 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6594 sg11540

lemma sg30487 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9275

lemma sg30488 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9312

lemma sg30489 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10817

lemma sg30490 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8808 sg9272

lemma sg30491 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9251

lemma sg30492 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9968

lemma sg30493 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10722

lemma sg30494 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9968

lemma sg30495 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9943

lemma sg30496 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9312

lemma sg30497 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3889 sg14510

lemma sg30498 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14519

lemma sg30499 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6991 sg11469

lemma sg30500 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6950 sg11475

lemma sg30501 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10374

lemma sg30502 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9351

lemma sg30503 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9272

lemma sg30504 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9546

lemma sg30505 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6992 sg11469

lemma sg30506 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6951 sg11475

lemma sg30507 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10485

lemma sg30508 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9352

lemma sg30509 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10818

lemma sg30510 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10485

lemma sg30511 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10376

lemma sg30512 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9313

lemma sg30513 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9969

lemma sg30514 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10723

lemma sg30515 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9969

lemma sg30516 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9944

lemma sg30517 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9944

lemma sg30518 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10711

lemma sg30519 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10374

lemma sg30520 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6952 sg11475

lemma sg30521 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9314

lemma sg30522 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9353

lemma sg30523 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9970

lemma sg30524 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10724

lemma sg30525 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9970

lemma sg30526 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9314

lemma sg30527 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9945

lemma sg30528 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9945

lemma sg30529 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10712

lemma sg30530 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9620

lemma sg30531 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10375

lemma sg30532 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9937

lemma sg30533 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9621

lemma sg30534 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14519

lemma sg30535 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6993 sg11469

lemma sg30536 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6953 sg11475

lemma sg30537 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10486

lemma sg30538 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9352

lemma sg30539 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,7,5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10819

end UniversalTensorSquare
end
end

end OAI
