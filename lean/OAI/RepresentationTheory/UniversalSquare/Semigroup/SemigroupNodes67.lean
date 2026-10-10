import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes52
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44

namespace OAI

/-! Semigroup Nodes 67. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg27340 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8657 sg9740

lemma sg27341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5547 sg12630

lemma sg27342 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5245 sg12693

lemma sg27343 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8453 sg10239

lemma sg27344 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9201

lemma sg27345 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9848

lemma sg27346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8736 sg9508

lemma sg27347 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8589 sg10088

lemma sg27348 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9202

lemma sg27349 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9856

lemma sg27350 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8720 sg9585

lemma sg27351 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8666 sg9730

lemma sg27352 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9856

lemma sg27353 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8677 sg9662

lemma sg27354 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8847 sg9162

lemma sg27355 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2241 sg15517

lemma sg27356 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2685 sg15013

lemma sg27357 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2870 sg14857

lemma sg27358 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5548 sg12630

lemma sg27359 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5246 sg12693

lemma sg27360 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10311

lemma sg27361 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9297

lemma sg27362 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8660 sg9732

lemma sg27363 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3766 sg14542

lemma sg27364 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5549 sg12630

lemma sg27365 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5247 sg12693

lemma sg27366 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10316

lemma sg27367 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9298

lemma sg27368 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9848

lemma sg27369 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8737 sg9500

lemma sg27370 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5248 sg12693

lemma sg27371 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10409

lemma sg27372 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9209

lemma sg27373 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10733

lemma sg27374 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10409

lemma sg27375 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8815 sg9210

lemma sg27376 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9857

lemma sg27377 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9586

lemma sg27378 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8367 sg10648

lemma sg27379 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9857

lemma sg27380 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10316

lemma sg27381 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9144

lemma sg27382 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5550 sg12630

lemma sg27383 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5249 sg12693

lemma sg27384 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8593 sg10088

lemma sg27385 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9299

lemma sg27386 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8657 sg9741

lemma sg27387 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8722 sg9585

lemma sg27388 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10317

lemma sg27389 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9300

lemma sg27390 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9850

lemma sg27391 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9510

lemma sg27392 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8818 sg9200

lemma sg27393 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9858

lemma sg27394 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9858

lemma sg27395 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8658 sg9741

lemma sg27396 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10312

lemma sg27397 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9145

lemma sg27398 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8376 sg10641

lemma sg27399 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9859

lemma sg27400 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9859

lemma sg27401 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10317

lemma sg27402 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9587

lemma sg27403 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10313

lemma sg27404 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9146

lemma sg27405 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9743

lemma sg27406 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2686 sg15013

lemma sg27407 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3767 sg14542

lemma sg27408 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5551 sg12630

lemma sg27409 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5253 sg12692

lemma sg27410 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8595 sg10087

lemma sg27411 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9298

lemma sg27412 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8660 sg9736

lemma sg27413 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9500

lemma sg27414 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5552 sg12630

lemma sg27415 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5254 sg12692

lemma sg27416 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10410

lemma sg27417 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9301

lemma sg27418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9849

lemma sg27419 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10410

lemma sg27420 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8596 sg10087

lemma sg27421 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9300

lemma sg27422 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9852

lemma sg27423 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9586

lemma sg27424 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8818 sg9203

lemma sg27425 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9860

lemma sg27426 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9860

lemma sg27427 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10318

lemma sg27428 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9730

lemma sg27429 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9147

lemma sg27430 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5255 sg12692

lemma sg27431 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10319

lemma sg27432 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9302

lemma sg27433 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9850

lemma sg27434 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9586

lemma sg27435 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8663 sg9733

lemma sg27436 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9303

lemma sg27437 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9861

lemma sg27438 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9861

lemma sg27439 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10319

lemma sg27440 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9588

lemma sg27441 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10314

lemma sg27442 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9148

lemma sg27443 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9854

lemma sg27444 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9589

lemma sg27445 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9205

lemma sg27446 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9149

lemma sg27447 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10313

lemma sg27448 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8605 sg10080

lemma sg27449 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9304

lemma sg27450 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9862

lemma sg27451 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9862

lemma sg27452 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8675 sg9677

lemma sg27453 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9855

lemma sg27454 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9590

lemma sg27455 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10315

lemma sg27456 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9150

lemma sg27457 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9747

lemma sg27458 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8736 sg9515

lemma sg27459 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9748

lemma sg27460 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8180 sg10862

lemma sg27461 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3768 sg14542

lemma sg27462 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5577 sg12620

lemma sg27463 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5256 sg12692

lemma sg27464 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8597 sg10087

lemma sg27465 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9301

lemma sg27466 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8765 sg9453

lemma sg27467 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8819 sg9203

lemma sg27468 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5257 sg12692

lemma sg27469 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8598 sg10087

lemma sg27470 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9302

lemma sg27471 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9852

lemma sg27472 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9204

lemma sg27473 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8663 sg9736

lemma sg27474 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9303

lemma sg27475 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9863

lemma sg27476 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9863

lemma sg27477 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8865 sg9045

lemma sg27478 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8819 sg9206

lemma sg27479 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9749

lemma sg27480 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8870 sg9041

lemma sg27481 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10320

lemma sg27482 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9304

lemma sg27483 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9864

lemma sg27484 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9864

lemma sg27485 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10320

lemma sg27486 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9854

lemma sg27487 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9588

lemma sg27488 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9737

lemma sg27489 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10314

lemma sg27490 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9589

lemma sg27491 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9751

lemma sg27492 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8396 sg10602

lemma sg27493 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9855

lemma sg27494 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9588

lemma sg27495 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9738

lemma sg27496 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9590

lemma sg27497 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10315

lemma sg27498 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8747 sg9496

lemma sg27499 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8778 sg9444

lemma sg27500 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8542 sg10115

lemma sg27501 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8675 sg9682

lemma sg27502 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10315

lemma sg27503 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8179 sg10863

lemma sg27504 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8847 sg9164

lemma sg27505 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9151

lemma sg27506 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8818 sg9207

lemma sg27507 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8179 sg10864

lemma sg27508 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10316

lemma sg27509 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9152

lemma sg27510 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8820 sg9200

lemma sg27511 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8818 sg9208

lemma sg27512 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9753

lemma sg27513 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9153

lemma sg27514 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10317

lemma sg27515 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9754

lemma sg27516 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8370 sg10648

lemma sg27517 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8818 sg9211

lemma sg27518 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10318

lemma sg27519 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8663 sg9741

lemma sg27520 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10319

lemma sg27521 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9756

lemma sg27522 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10317

lemma sg27523 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9738

lemma sg27524 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9758

lemma sg27525 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10317

lemma sg27526 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8823 sg9203

lemma sg27527 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8663 sg9744

lemma sg27528 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9215

lemma sg27529 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10318

lemma sg27530 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10320

lemma sg27531 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10319

lemma sg27532 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9217

lemma sg27533 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9761

lemma sg27534 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10319

lemma sg27535 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8748 sg9501

lemma sg27536 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8870 sg9045

lemma sg27537 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9749

lemma sg27538 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8179 sg10865

lemma sg27539 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10320

lemma sg27540 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9751

lemma sg27541 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10320

lemma sg27542 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,7,7,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8883 sg8991

lemma sg27543 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8180 sg10863

lemma sg27544 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8847 sg9167

lemma sg27545 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8487 sg10190

lemma sg27546 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9154

lemma sg27547 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8820 sg9207

lemma sg27548 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8818 sg9219

lemma sg27549 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8677 sg9676

lemma sg27550 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9208

lemma sg27551 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8661 sg9753

lemma sg27552 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9210

lemma sg27553 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9220

lemma sg27554 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8823 sg9207

lemma sg27555 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9211

lemma sg27556 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8661 sg9755

lemma sg27557 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8823 sg9210

lemma sg27558 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9753

lemma sg27559 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9221

lemma sg27560 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9222

lemma sg27561 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9214

lemma sg27562 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9223

lemma sg27563 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8823 sg9211

lemma sg27564 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9755

lemma sg27565 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9224

lemma sg27566 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9756

lemma sg27567 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9225

lemma sg27568 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9226

lemma sg27569 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8884 sg8991

lemma sg27570 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8823 sg9215

lemma sg27571 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9759

lemma sg27572 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9227

lemma sg27573 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,7,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8818 sg9228

lemma sg27574 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,7,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8663 sg9761

lemma sg27575 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,8,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8597 sg10095

lemma sg27576 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,8,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8173 sg11048

lemma sg27577 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,8,8,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8173 sg11049

lemma sg27578 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8183 sg10863

lemma sg27579 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8867 sg9065

lemma sg27580 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8551 sg10116

lemma sg27581 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8185 sg10863

lemma sg27582 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8820 sg9219

lemma sg27583 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8552 sg10116

lemma sg27584 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8869 sg9065

lemma sg27585 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9753

lemma sg27586 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9220

lemma sg27587 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8848 sg9166

lemma sg27588 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8823 sg9219

lemma sg27589 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8668 sg9755

lemma sg27590 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8823 sg9220

lemma sg27591 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9221

lemma sg27592 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9222

lemma sg27593 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9223

lemma sg27594 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8670 sg9755

lemma sg27595 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9224

lemma sg27596 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8823 sg9222

lemma sg27597 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9225

lemma sg27598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9226

lemma sg27599 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,7,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8823 sg9224

lemma sg27600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,7,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9227

lemma sg27601 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,7,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8820 sg9228

lemma sg27602 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,8,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8823 sg9227

lemma sg27603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,8,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8823 sg9228

lemma sg27604 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,9,9,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8208 sg10857

lemma sg27605 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg21657

lemma sg27606 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg21658

lemma sg27607 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg21659

lemma sg27608 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg21660

lemma sg27609 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg21661

lemma sg27610 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg25 sg21662

lemma sg27611 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21663

lemma sg27612 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21664

lemma sg27613 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21665

lemma sg27614 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21666

lemma sg27615 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21667

lemma sg27616 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg24 sg21668

lemma sg27617 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg24 sg21669

lemma sg27618 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg21021

lemma sg27619 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg21650

lemma sg27620 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg21651

lemma sg27621 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg21652

lemma sg27622 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg21653

lemma sg27623 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg21654

lemma sg27624 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg72 sg21655

lemma sg27625 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg21000

lemma sg27626 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1702 sg18259

lemma sg27627 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg126 sg21628

lemma sg27628 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg126 sg21629

lemma sg27629 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg126 sg21630

lemma sg27630 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg126 sg21631

lemma sg27631 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg126 sg21632

lemma sg27632 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg126 sg21633

lemma sg27633 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg962 sg21126

lemma sg27634 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg145 sg21622

lemma sg27635 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg21180

lemma sg27636 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg145 sg21623

lemma sg27637 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg145 sg21624

lemma sg27638 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg145 sg21625

lemma sg27639 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg145 sg21626

lemma sg27640 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg145 sg21627

lemma sg27641 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg967 sg21123

lemma sg27642 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1309 sg20967

lemma sg27643 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg288 sg21339

lemma sg27644 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg21181

lemma sg27645 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg288 sg21340

lemma sg27646 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg288 sg21341

lemma sg27647 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg288 sg21342

lemma sg27648 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg288 sg21343

lemma sg27649 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg288 sg21344

lemma sg27650 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg21328

lemma sg27651 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg548 sg21265

lemma sg27652 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg21329

lemma sg27653 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg21182

lemma sg27654 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg21330

lemma sg27655 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg21331

lemma sg27656 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg331 sg21332

lemma sg27657 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg331 sg21333

lemma sg27658 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg548 sg21266

lemma sg27659 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg548 sg21267

lemma sg27660 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg21183

lemma sg27661 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10196

lemma sg27662 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11287

lemma sg27663 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6901 sg11486

lemma sg27664 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6124 sg11758

lemma sg27665 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8 sg21670

lemma sg27666 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10197

lemma sg27667 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10173

lemma sg27668 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7456 sg11261

lemma sg27669 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6903 sg11481

lemma sg27670 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10174

lemma sg27671 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8508 sg10168

lemma sg27672 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7458 sg11257

lemma sg27673 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6125 sg11757

lemma sg27674 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8517 sg10167

lemma sg27675 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg7460 sg11256

lemma sg27676 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6363 sg11739

lemma sg27677 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg21022

lemma sg27678 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg21650

lemma sg27679 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg21651

lemma sg27680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg21652

lemma sg27681 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg21653

lemma sg27682 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg21654

lemma sg27683 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg73 sg21655

lemma sg27684 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg21001

lemma sg27685 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1702 sg18260

lemma sg27686 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg127 sg21628

lemma sg27687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg127 sg21629

lemma sg27688 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg127 sg21630

lemma sg27689 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg127 sg21631

lemma sg27690 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg127 sg21632

lemma sg27691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg127 sg21633

lemma sg27692 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1290 sg21000

lemma sg27693 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1709 sg18248

lemma sg27694 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1702 sg18261

lemma sg27695 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg146 sg21623

lemma sg27696 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg146 sg21624

lemma sg27697 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg146 sg21625

lemma sg27698 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg146 sg21626

lemma sg27699 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg146 sg21627

lemma sg27700 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg963 sg21126

lemma sg27701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1309 sg20969

lemma sg27702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg850 sg21168

lemma sg27703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg21184

lemma sg27704 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg289 sg21340

lemma sg27705 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg289 sg21341

lemma sg27706 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg289 sg21342

lemma sg27707 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg289 sg21343

lemma sg27708 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg289 sg21344

lemma sg27709 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg987 sg21107

lemma sg27710 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1310 sg20967

lemma sg27711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1309 sg20970

lemma sg27712 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg850 sg21169

lemma sg27713 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg21185

lemma sg27714 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg332 sg21330

lemma sg27715 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg332 sg21331

lemma sg27716 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg332 sg21332

lemma sg27717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg332 sg21333

lemma sg27718 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg549 sg21265

lemma sg27719 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg561 sg21247

lemma sg27720 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg850 sg21170

lemma sg27721 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg21186

lemma sg27722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10198

lemma sg27723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11288

lemma sg27724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6901 sg11487

lemma sg27725 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6124 sg11759

lemma sg27726 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg561 sg21248

lemma sg27727 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg850 sg21171

lemma sg27728 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10199

lemma sg27729 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10175

lemma sg27730 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7456 sg11262

lemma sg27731 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6903 sg11482

lemma sg27732 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8468 sg10200

lemma sg27733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8490 sg10176

lemma sg27734 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8491 sg10173

lemma sg27735 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7457 sg11261

lemma sg27736 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6904 sg11481

lemma sg27737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8491 sg10174

lemma sg27738 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8509 sg10168

lemma sg27739 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg7459 sg11257

end UniversalTensorSquare
end
end

end OAI
