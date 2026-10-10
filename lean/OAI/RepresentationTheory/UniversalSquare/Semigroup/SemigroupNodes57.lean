import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes52
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes47
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes43
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes46

namespace OAI

/-! Semigroup Nodes 57. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg23340 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6416 sg6838

lemma sg23341 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6371 sg7103

lemma sg23342 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6660

lemma sg23343 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7755

lemma sg23344 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7191

lemma sg23345 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7755

lemma sg23346 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7697

lemma sg23347 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7209

lemma sg23348 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7210

lemma sg23349 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7698

lemma sg23350 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7210

lemma sg23351 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7441

lemma sg23352 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6298 sg7440

lemma sg23353 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7756

lemma sg23354 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7211

lemma sg23355 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6299 sg7440

lemma sg23356 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7757

lemma sg23357 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7212

lemma sg23358 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7758

lemma sg23359 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7213

lemma sg23360 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7442

lemma sg23361 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7443

lemma sg23362 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6424 sg6837

lemma sg23363 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7759

lemma sg23364 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7214

lemma sg23365 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7444

lemma sg23366 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7215

lemma sg23367 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7445

lemma sg23368 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7446

lemma sg23369 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6421 sg6839

lemma sg23370 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7760

lemma sg23371 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7216

lemma sg23372 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6424 sg6839

lemma sg23373 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7761

lemma sg23374 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7217

lemma sg23375 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7447

lemma sg23376 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7218

lemma sg23377 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6296 sg7448

lemma sg23378 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7762

lemma sg23379 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7219

lemma sg23380 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7220

lemma sg23381 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6442 sg6796

lemma sg23382 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,7,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7763

lemma sg23383 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,7,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7221

lemma sg23384 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6413 sg6852

lemma sg23385 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,7,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7764

lemma sg23386 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,7,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7222

lemma sg23387 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,7,7,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7223

lemma sg23388 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1313 sg14718

lemma sg23389 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1714 sg14409

lemma sg23390 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1814 sg14308

lemma sg23391 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg14751

lemma sg23392 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg14755

lemma sg23393 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg19570

lemma sg23394 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg342 sg19571

lemma sg23395 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1314 sg14718

lemma sg23396 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1715 sg14409

lemma sg23397 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1815 sg14308

lemma sg23398 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2178 sg12910

lemma sg23399 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1289 sg14752

lemma sg23400 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2667 sg12587

lemma sg23401 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5365 sg8717

lemma sg23402 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4729 sg10580

lemma sg23403 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1315 sg14718

lemma sg23404 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1716 sg14409

lemma sg23405 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1816 sg14308

lemma sg23406 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3214 sg11746

lemma sg23407 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2222 sg12862

lemma sg23408 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6221 sg7491

lemma sg23409 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5366 sg8714

lemma sg23410 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6158 sg7625

lemma sg23411 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1461 sg14698

lemma sg23412 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3215 sg11746

lemma sg23413 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3212 sg11747

lemma sg23414 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6222 sg7491

lemma sg23415 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6209 sg7493

lemma sg23416 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7206

lemma sg23417 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6159 sg7625

lemma sg23418 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3790 sg11539

lemma sg23419 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6223 sg7491

lemma sg23420 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6670

lemma sg23421 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7224

lemma sg23422 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6367 sg7206

lemma sg23423 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6671

lemma sg23424 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7765

lemma sg23425 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7702

lemma sg23426 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6296 sg7449

lemma sg23427 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg6445 sg6790

lemma sg23428 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7765

lemma sg23429 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1316 sg14718

lemma sg23430 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1717 sg14409

lemma sg23431 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1817 sg14308

lemma sg23432 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3216 sg11746

lemma sg23433 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2178 sg12911

lemma sg23434 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6224 sg7491

lemma sg23435 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5366 sg8715

lemma sg23436 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6160 sg7625

lemma sg23437 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1718 sg14409

lemma sg23438 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1818 sg14308

lemma sg23439 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3217 sg11746

lemma sg23440 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3791 sg11539

lemma sg23441 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6225 sg7491

lemma sg23442 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6211 sg7493

lemma sg23443 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6368 sg7206

lemma sg23444 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6161 sg7625

lemma sg23445 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3218 sg11746

lemma sg23446 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3792 sg11539

lemma sg23447 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6226 sg7491

lemma sg23448 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6672

lemma sg23449 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7207

lemma sg23450 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6406 sg6863

lemma sg23451 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6227 sg7491

lemma sg23452 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6673

lemma sg23453 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7225

lemma sg23454 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7207

lemma sg23455 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6298 sg7449

lemma sg23456 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7766

lemma sg23457 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7703

lemma sg23458 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7766

lemma sg23459 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7225

lemma sg23460 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1819 sg14308

lemma sg23461 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3219 sg11746

lemma sg23462 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3793 sg11539

lemma sg23463 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6228 sg7491

lemma sg23464 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6674

lemma sg23465 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6415 sg6850

lemma sg23466 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6408 sg6863

lemma sg23467 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3794 sg11539

lemma sg23468 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6229 sg7491

lemma sg23469 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6675

lemma sg23470 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6366 sg7208

lemma sg23471 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6416 sg6850

lemma sg23472 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6299 sg7449

lemma sg23473 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6676

lemma sg23474 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7767

lemma sg23475 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7208

lemma sg23476 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7767

lemma sg23477 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7704

lemma sg23478 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7226

lemma sg23479 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6230 sg7491

lemma sg23480 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6481 sg6677

lemma sg23481 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6147 sg7768

lemma sg23482 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6416 sg6851

lemma sg23483 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7768

lemma sg23484 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6364 sg7227

lemma sg23485 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6150 sg7705

lemma sg23486 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7227

lemma sg23487 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6367 sg7210

lemma sg23488 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6421 sg6849

lemma sg23489 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7769

lemma sg23490 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7228

lemma sg23491 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6424 sg6849

lemma sg23492 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,5,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7770

lemma sg23493 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7229

lemma sg23494 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7230

lemma sg23495 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7771

lemma sg23496 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,6,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6372 sg7118

lemma sg23497 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,6,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7772

lemma sg23498 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,6,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6365 sg7231

lemma sg23499 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,6,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7773

lemma sg23500 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,7,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6315 sg7376

lemma sg23501 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,7,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7774

lemma sg23502 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,8,8,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6315 sg7383

lemma sg23503 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1317 sg14718

lemma sg23504 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1719 sg14409

lemma sg23505 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg963 sg15154

lemma sg23506 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1814 sg14309

lemma sg23507 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg19572

lemma sg23508 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2667 sg12588

lemma sg23509 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5366 sg8717

lemma sg23510 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4730 sg10580

lemma sg23511 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6417 sg6853

lemma sg23512 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7775

lemma sg23513 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6421 sg6853

lemma sg23514 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7776

lemma sg23515 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6424 sg6853

lemma sg23516 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7777

lemma sg23517 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6372 sg7135

lemma sg23518 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6148 sg7778

lemma sg23519 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,9,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6315 sg7392

lemma sg23520 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg990 sg15055

lemma sg23521 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1317 sg14719

lemma sg23522 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg985 sg15057

lemma sg23523 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3224 sg11745

lemma sg23524 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg958 sg15155

lemma sg23525 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6275 sg7487

lemma sg23526 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5297 sg8790

lemma sg23527 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6348 sg7288

lemma sg23528 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6371 sg7157

lemma sg23529 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [10,10,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6372 sg7157

lemma sg23530 : RowSquare [6,6,3,3,3,3,2,2,2,2,2,2,2,1,1] [5,5,5,5,5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7817 sg8007

lemma sg23531 : RowSquare [8,8,3,3,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg14796

lemma sg23532 : RowSquare [8,8,3,3,2,2,2,2,2,2,2,2,1,1] [6,6,6,6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1844 sg14797

lemma sg23533 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [6,5,5,5,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg7809 sg8210

lemma sg23534 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [8,8,8,8,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1868 sg14846

lemma sg23535 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [8,8,8,8,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7786 sg8273

lemma sg23536 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [8,8,8,8,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7254 sg8619

lemma sg23537 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [8,8,8,8,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7787 sg8273

lemma sg23538 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [9,9,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg8639

lemma sg23539 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [9,9,9,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1723 sg15101

lemma sg23540 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg8640

lemma sg23541 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,9,7,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg8641

lemma sg23542 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,9,8,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg8642

lemma sg23543 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg990 sg18027

lemma sg23544 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1317 sg15596

lemma sg23545 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg985 sg18028

lemma sg23546 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg562 sg21038

lemma sg23547 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg21112

lemma sg23548 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg21113

lemma sg23549 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg21114

lemma sg23550 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg21115

lemma sg23551 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg367 sg21116

lemma sg23552 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1322 sg15595

lemma sg23553 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1725 sg15100

lemma sg23554 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1325 sg15557

lemma sg23555 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1744 sg15047

lemma sg23556 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2237 sg14696

lemma sg23557 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2680 sg14209

lemma sg23558 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg871 sg19177

lemma sg23559 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2667 sg14210

lemma sg23560 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg871 sg19178

lemma sg23561 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg871 sg19179

lemma sg23562 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg986 sg18028

lemma sg23563 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1746 sg15045

lemma sg23564 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1849 sg14977

lemma sg23565 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2223 sg14697

lemma sg23566 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg887 sg18279

lemma sg23567 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6221 sg10105

lemma sg23568 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg887 sg18280

lemma sg23569 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6891 sg8717

lemma sg23570 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1325 sg15558

lemma sg23571 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2246 sg14695

lemma sg23572 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg562 sg21039

lemma sg23573 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6222 sg10105

lemma sg23574 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg569 sg21036

lemma sg23575 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7255 sg8624

lemma sg23576 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg569 sg21037

lemma sg23577 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg14976

lemma sg23578 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6223 sg10105

lemma sg23579 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5242 sg11507

lemma sg23580 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8281

lemma sg23581 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg7239 sg8638

lemma sg23582 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5243 sg11507

lemma sg23583 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6900 sg8707

lemma sg23584 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7512 sg8404

lemma sg23585 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg8643

lemma sg23586 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg7240 sg8638

lemma sg23587 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1726 sg15100

lemma sg23588 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1746 sg15046

lemma sg23589 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2151 sg14708

lemma sg23590 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2238 sg14696

lemma sg23591 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2681 sg14209

lemma sg23592 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1326 sg15556

lemma sg23593 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6224 sg10105

lemma sg23594 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2667 sg14211

lemma sg23595 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6892 sg8717

lemma sg23596 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1745 sg15047

lemma sg23597 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2239 sg14696

lemma sg23598 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2682 sg14209

lemma sg23599 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2693 sg14086

lemma sg23600 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6225 sg10105

lemma sg23601 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1238 sg15601

lemma sg23602 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7791 sg8275

lemma sg23603 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1238 sg15602

lemma sg23604 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2683 sg14209

lemma sg23605 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2249 sg14678

lemma sg23606 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6226 sg10105

lemma sg23607 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5912 sg10861

lemma sg23608 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7783 sg8281

lemma sg23609 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg7792 sg8275

lemma sg23610 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6227 sg10105

lemma sg23611 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5913 sg10861

lemma sg23612 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8282

lemma sg23613 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7512 sg8405

lemma sg23614 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg8644

lemma sg23615 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7798 sg8272

lemma sg23616 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7781 sg8282

lemma sg23617 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1868 sg14847

lemma sg23618 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3169 sg12947

lemma sg23619 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3777 sg12701

lemma sg23620 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6228 sg10105

lemma sg23621 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5246 sg11507

lemma sg23622 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7786 sg8281

lemma sg23623 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg7242 sg8638

lemma sg23624 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3778 sg12701

lemma sg23625 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6229 sg10105

lemma sg23626 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5919 sg10852

lemma sg23627 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6891 sg8718

lemma sg23628 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7512 sg8406

lemma sg23629 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg8645

lemma sg23630 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5248 sg11507

lemma sg23631 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8283

lemma sg23632 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7243 sg8638

lemma sg23633 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7781 sg8283

lemma sg23634 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6230 sg10105

lemma sg23635 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5920 sg10852

lemma sg23636 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6900 sg8708

lemma sg23637 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg7526 sg8400

lemma sg23638 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8284

lemma sg23639 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7781 sg8284

lemma sg23640 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6893 sg8717

lemma sg23641 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [10,10,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7232 sg8646

lemma sg23642 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,5,5,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6883 sg8719

lemma sg23643 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,5,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7808 sg8211

lemma sg23644 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,5,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8286

lemma sg23645 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,5,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8287

lemma sg23646 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,5,5,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7805 sg8212

lemma sg23647 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7790 sg8276

lemma sg23648 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7790 sg8277

lemma sg23649 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7784 sg8286

lemma sg23650 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7790 sg8278

lemma sg23651 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7784 sg8287

lemma sg23652 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4652 sg11786

lemma sg23653 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,6,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6124 sg10575

lemma sg23654 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7786 sg8285

lemma sg23655 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7790 sg8279

lemma sg23656 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7790 sg8280

lemma sg23657 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,6,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7797 sg8274

lemma sg23658 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [11,8,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8289

lemma sg23659 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,5,5,5,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7790 sg8286

lemma sg23660 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,5,5,5,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7790 sg8287

lemma sg23661 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8291

lemma sg23662 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,5,5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8292

lemma sg23663 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,5,5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7780 sg8293

lemma sg23664 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7790 sg8288

lemma sg23665 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,5,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4652 sg11787

lemma sg23666 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6855 sg8769

lemma sg23667 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7786 sg8290

lemma sg23668 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6901 sg8716

lemma sg23669 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,6,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6855 sg8770

lemma sg23670 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6701 sg8887

lemma sg23671 : RowSquare [11,10,4,3,2,2,2,2,2,2,1] [12,6,6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7779 sg8294

lemma sg23672 : RowSquare [11,10,4,3,2,2,2,2,2,2,1,1] [7,5,5,5,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg23533

lemma sg23673 : RowSquare [9,8,3,3,2,2,2,2,2,2,2,2,2,1,1] [7,6,6,6,6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2247 sg15690

lemma sg23674 : RowSquare [9,8,3,3,2,2,2,2,2,2,2,2,2,1,1] [7,6,6,6,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2247 sg15691

lemma sg23675 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,6,6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg74 sg21649

lemma sg23676 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,6,6,6,6,5] := by
  exact rowSquare_join (by decide) sg74 sg21648

lemma sg23677 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,6,6,5,5] := by
  exact rowSquare_join (by decide) sg8432 sg10195

lemma sg23678 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,6,6,6,4] := by
  exact rowSquare_join (by decide) sg74 sg21644

lemma sg23679 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,5,5,5] := by
  exact rowSquare_join (by decide) sg8432 sg10193

lemma sg23680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,6,5,4] := by
  exact rowSquare_join (by decide) sg8432 sg10194

lemma sg23681 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7247 sg11435

lemma sg23682 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8748 sg9444

lemma sg23683 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9468

lemma sg23684 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7235 sg11448

lemma sg23685 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,2,2,2,2] := by
  exact rowSquare_join (by decide) sg7247 sg11437

lemma sg23686 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8428 sg10195

lemma sg23687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4747 sg12931

lemma sg23688 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,3,2,2,1] := by
  exact rowSquare_join (by decide) sg7247 sg11438

lemma sg23689 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6398 sg11736

lemma sg23690 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,3,3,2] := by
  exact rowSquare_join (by decide) sg4747 sg12932

lemma sg23691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8429 sg10195

lemma sg23692 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8430 sg10195

lemma sg23693 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,4,2,2] := by
  exact rowSquare_join (by decide) sg74 sg21645

lemma sg23694 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,4,3,1] := by
  exact rowSquare_join (by decide) sg7451 sg11286

lemma sg23695 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,5,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg21646

lemma sg23696 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,5,2,1] := by
  exact rowSquare_join (by decide) sg8431 sg10195

lemma sg23697 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [7,7,7,7,7,6,1,1] := by
  exact rowSquare_join (by decide) sg74 sg21647

lemma sg23698 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,4,4,4,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8494 sg10167

lemma sg23699 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,4,4,4,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10245

lemma sg23700 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,4,4,4,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10196

lemma sg23701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,4,4,4,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10246

lemma sg23702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,4,4,4,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10247

lemma sg23703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,4,4,4,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg8648 sg9684

lemma sg23704 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8498 sg10167

lemma sg23705 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10248

lemma sg23706 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10198

lemma sg23707 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10249

lemma sg23708 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9683

lemma sg23709 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10250

lemma sg23710 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9686

lemma sg23711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10200

lemma sg23712 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8648 sg9687

lemma sg23713 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8499 sg10167

lemma sg23714 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10251

lemma sg23715 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10201

lemma sg23716 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10252

lemma sg23717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8724 sg9445

lemma sg23718 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10253

lemma sg23719 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9689

lemma sg23720 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10254

lemma sg23721 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10203

lemma sg23722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9690

lemma sg23723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8798 sg9160

lemma sg23724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10255

lemma sg23725 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10204

lemma sg23726 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10256

lemma sg23727 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8724 sg9447

lemma sg23728 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10257

lemma sg23729 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9692

lemma sg23730 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8750 sg9443

lemma sg23731 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10258

lemma sg23732 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10206

lemma sg23733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9693

lemma sg23734 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10615

lemma sg23735 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9694

lemma sg23736 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9161

lemma sg23737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg8830 sg9158

lemma sg23738 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8724 sg9448

lemma sg23739 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,5,5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10259

end UniversalTensorSquare
end
end

end OAI
