import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24

namespace OAI

/-! Semigroup Nodes 62. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg25340 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8770 sg9442

lemma sg25341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8770 sg9443

lemma sg25342 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7254 sg11436

lemma sg25343 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8870 sg8999

lemma sg25344 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9529

lemma sg25345 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8556 sg10095

lemma sg25346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8189 sg10858

lemma sg25347 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14503

lemma sg25348 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8770 sg9444

lemma sg25349 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8721 sg9530

lemma sg25350 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8557 sg10095

lemma sg25351 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8870 sg9000

lemma sg25352 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8558 sg10095

lemma sg25353 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8870 sg9001

lemma sg25354 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg7795 sg11245

lemma sg25355 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8722 sg9530

lemma sg25356 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10095

lemma sg25357 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8870 sg9002

lemma sg25358 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8379 sg10610

lemma sg25359 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7789 sg11254

lemma sg25360 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8559 sg10096

lemma sg25361 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,8,8,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7796 sg11246

lemma sg25362 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8511 sg10167

lemma sg25363 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10321

lemma sg25364 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10245

lemma sg25365 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10322

lemma sg25366 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8724 sg9469

lemma sg25367 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10323

lemma sg25368 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9763

lemma sg25369 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10247

lemma sg25370 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,4,4,4,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8648 sg9764

lemma sg25371 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8513 sg10167

lemma sg25372 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10324

lemma sg25373 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10248

lemma sg25374 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10325

lemma sg25375 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9762

lemma sg25376 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10326

lemma sg25377 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9767

lemma sg25378 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10327

lemma sg25379 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10250

lemma sg25380 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9768

lemma sg25381 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,4,4,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8423 sg10247

lemma sg25382 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8514 sg10167

lemma sg25383 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10328

lemma sg25384 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10251

lemma sg25385 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10329

lemma sg25386 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8724 sg9471

lemma sg25387 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10330

lemma sg25388 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9770

lemma sg25389 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9532

lemma sg25390 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10331

lemma sg25391 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10253

lemma sg25392 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9771

lemma sg25393 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10254

lemma sg25394 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9772

lemma sg25395 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9175

lemma sg25396 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg8860 sg9078

lemma sg25397 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10255

lemma sg25398 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10332

lemma sg25399 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8724 sg9473

lemma sg25400 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10333

lemma sg25401 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9774

lemma sg25402 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8750 sg9447

lemma sg25403 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10334

lemma sg25404 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10257

lemma sg25405 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9775

lemma sg25406 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10335

lemma sg25407 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10258

lemma sg25408 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9776

lemma sg25409 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9177

lemma sg25410 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9178

lemma sg25411 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9178

lemma sg25412 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg8873 sg8984

lemma sg25413 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8750 sg9448

lemma sg25414 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10336

lemma sg25415 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10259

lemma sg25416 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9777

lemma sg25417 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8494 sg10172

lemma sg25418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10337

lemma sg25419 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10260

lemma sg25420 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9778

lemma sg25421 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8653 sg9696

lemma sg25422 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10660

lemma sg25423 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9779

lemma sg25424 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8724 sg9474

lemma sg25425 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8725 sg9474

lemma sg25426 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8873 sg8985

lemma sg25427 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8381 sg10601

lemma sg25428 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8873 sg8986

lemma sg25429 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8500 sg10168

lemma sg25430 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10129

lemma sg25431 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8481 sg10174

lemma sg25432 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8529 sg10099

lemma sg25433 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8530 sg10099

lemma sg25434 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg8873 sg8987

lemma sg25435 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8529 sg10100

lemma sg25436 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8530 sg10100

lemma sg25437 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8561 sg10085

lemma sg25438 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg8873 sg8988

lemma sg25439 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg7248 sg11439

lemma sg25440 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8560 sg10086

lemma sg25441 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg8561 sg10086

lemma sg25442 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg8562 sg10086

lemma sg25443 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,5,5,5,5,5,5,3,1] := by
  exact rowSquare_join (by decide) sg6400 sg11737

lemma sg25444 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8515 sg10167

lemma sg25445 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10338

lemma sg25446 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10261

lemma sg25447 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10339

lemma sg25448 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9766

lemma sg25449 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10340

lemma sg25450 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9781

lemma sg25451 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8727 sg9470

lemma sg25452 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10341

lemma sg25453 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10263

lemma sg25454 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9782

lemma sg25455 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10264

lemma sg25456 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9783

lemma sg25457 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10250

lemma sg25458 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,4,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg8804 sg9174

lemma sg25459 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10342

lemma sg25460 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10265

lemma sg25461 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10343

lemma sg25462 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9769

lemma sg25463 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10344

lemma sg25464 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9786

lemma sg25465 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9534

lemma sg25466 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10345

lemma sg25467 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10267

lemma sg25468 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9787

lemma sg25469 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10346

lemma sg25470 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10268

lemma sg25471 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9788

lemma sg25472 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10253

lemma sg25473 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9772

lemma sg25474 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10254

lemma sg25475 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg8860 sg9079

lemma sg25476 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9773

lemma sg25477 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10347

lemma sg25478 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9789

lemma sg25479 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8727 sg9473

lemma sg25480 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10348

lemma sg25481 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10270

lemma sg25482 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9790

lemma sg25483 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9534

lemma sg25484 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10349

lemma sg25485 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10271

lemma sg25486 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9791

lemma sg25487 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10257

lemma sg25488 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10272

lemma sg25489 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9792

lemma sg25490 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9776

lemma sg25491 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10258

lemma sg25492 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8861 sg9010

lemma sg25493 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9178

lemma sg25494 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8861 sg9011

lemma sg25495 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8753 sg9448

lemma sg25496 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10350

lemma sg25497 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10273

lemma sg25498 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9793

lemma sg25499 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10259

lemma sg25500 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10351

lemma sg25501 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10274

lemma sg25502 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9794

lemma sg25503 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9778

lemma sg25504 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10260

lemma sg25505 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8861 sg9013

lemma sg25506 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9779

lemma sg25507 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8347 sg10660

lemma sg25508 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9474

lemma sg25509 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8861 sg9014

lemma sg25510 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8876 sg8986

lemma sg25511 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8524 sg10130

lemma sg25512 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8484 sg10174

lemma sg25513 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10129

lemma sg25514 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8530 sg10102

lemma sg25515 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10099

lemma sg25516 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg8861 sg9015

lemma sg25517 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8531 sg10100

lemma sg25518 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10100

lemma sg25519 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9016

lemma sg25520 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg8876 sg8988

lemma sg25521 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg8563 sg10086

lemma sg25522 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,5,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg8564 sg10086

lemma sg25523 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8524 sg10131

lemma sg25524 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8838 sg9159

lemma sg25525 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8724 sg9481

lemma sg25526 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8345 sg10668

lemma sg25527 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9796

lemma sg25528 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9536

lemma sg25529 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10352

lemma sg25530 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10669

lemma sg25531 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9797

lemma sg25532 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9471

lemma sg25533 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10353

lemma sg25534 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10275

lemma sg25535 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9798

lemma sg25536 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9187

lemma sg25537 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10276

lemma sg25538 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9799

lemma sg25539 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9188

lemma sg25540 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9188

lemma sg25541 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9080

lemma sg25542 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10254

lemma sg25543 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8860 sg9081

lemma sg25544 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9537

lemma sg25545 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10354

lemma sg25546 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10672

lemma sg25547 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9800

lemma sg25548 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9536

lemma sg25549 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10355

lemma sg25550 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10277

lemma sg25551 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9801

lemma sg25552 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9190

lemma sg25553 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10356

lemma sg25554 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10278

lemma sg25555 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9802

lemma sg25556 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9191

lemma sg25557 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9191

lemma sg25558 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9082

lemma sg25559 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9192

lemma sg25560 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9192

lemma sg25561 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10258

lemma sg25562 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9083

lemma sg25563 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8350 sg10657

lemma sg25564 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9536

lemma sg25565 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10357

lemma sg25566 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10279

lemma sg25567 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9803

lemma sg25568 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9193

lemma sg25569 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9193

lemma sg25570 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9084

lemma sg25571 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10280

lemma sg25572 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9804

lemma sg25573 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8724 sg9488

lemma sg25574 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8725 sg9488

lemma sg25575 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10260

lemma sg25576 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9085

lemma sg25577 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9539

lemma sg25578 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8751 sg9463

lemma sg25579 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9086

lemma sg25580 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg9014

lemma sg25581 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8529 sg10104

lemma sg25582 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8530 sg10104

lemma sg25583 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8526 sg10129

lemma sg25584 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8561 sg10094

lemma sg25585 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg8860 sg9087

lemma sg25586 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg8862 sg9015

lemma sg25587 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10100

lemma sg25588 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg8862 sg9016

lemma sg25589 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg8566 sg10086

lemma sg25590 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9537

lemma sg25591 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10358

lemma sg25592 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10677

lemma sg25593 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9805

lemma sg25594 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8798 sg9194

lemma sg25595 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9537

lemma sg25596 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10359

lemma sg25597 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10281

lemma sg25598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9806

lemma sg25599 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9195

lemma sg25600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9195

lemma sg25601 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8873 sg8999

lemma sg25602 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10282

lemma sg25603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9807

lemma sg25604 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9196

lemma sg25605 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9196

lemma sg25606 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8751 sg9464

lemma sg25607 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8752 sg9464

lemma sg25608 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8750 sg9465

lemma sg25609 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8751 sg9465

lemma sg25610 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8752 sg9465

lemma sg25611 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10658

lemma sg25612 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10360

lemma sg25613 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10283

lemma sg25614 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9808

lemma sg25615 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8797 sg9197

lemma sg25616 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8798 sg9197

lemma sg25617 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8751 sg9466

lemma sg25618 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8873 sg9000

lemma sg25619 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8724 sg9492

lemma sg25620 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8725 sg9492

lemma sg25621 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8872 sg9001

lemma sg25622 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8751 sg9467

lemma sg25623 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8873 sg9001

lemma sg25624 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8350 sg10659

lemma sg25625 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8568 sg10086

lemma sg25626 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8350 sg10660

lemma sg25627 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8560 sg10098

lemma sg25628 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8561 sg10098

lemma sg25629 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg8562 sg10098

lemma sg25630 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8538 sg10100

lemma sg25631 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg8863 sg9015

lemma sg25632 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg8863 sg9016

lemma sg25633 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6919 sg11472

lemma sg25634 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10284

lemma sg25635 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10284

lemma sg25636 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9809

lemma sg25637 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10284

lemma sg25638 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9809

lemma sg25639 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8434 sg10230

lemma sg25640 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8723 sg9493

lemma sg25641 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8724 sg9493

lemma sg25642 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8725 sg9493

lemma sg25643 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8872 sg9002

lemma sg25644 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8751 sg9468

lemma sg25645 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8873 sg9002

lemma sg25646 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8881 sg8986

lemma sg25647 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8471 sg10195

lemma sg25648 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8472 sg10195

lemma sg25649 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8473 sg10195

lemma sg25650 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8474 sg10195

lemma sg25651 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8540 sg10100

lemma sg25652 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8430 sg10260

lemma sg25653 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8351 sg10660

lemma sg25654 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8500 sg10172

lemma sg25655 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8481 sg10182

lemma sg25656 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg8352 sg10659

lemma sg25657 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg8352 sg10660

lemma sg25658 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg335 sg21316

lemma sg25659 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,6,6,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg331 sg21325

lemma sg25660 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,3,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8516 sg10167

lemma sg25661 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,3,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8415 sg10361

lemma sg25662 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10285

lemma sg25663 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10362

lemma sg25664 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9780

lemma sg25665 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10363

lemma sg25666 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9812

lemma sg25667 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8727 sg9475

lemma sg25668 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10364

lemma sg25669 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10287

lemma sg25670 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9813

lemma sg25671 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10365

lemma sg25672 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10288

lemma sg25673 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9814

lemma sg25674 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10263

lemma sg25675 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9783

lemma sg25676 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10264

lemma sg25677 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,4,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg8861 sg9017

lemma sg25678 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8418 sg10289

lemma sg25679 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8415 sg10366

lemma sg25680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9785

lemma sg25681 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10367

lemma sg25682 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9816

lemma sg25683 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9541

lemma sg25684 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10368

lemma sg25685 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10291

lemma sg25686 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9817

lemma sg25687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9475

lemma sg25688 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10369

lemma sg25689 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10292

lemma sg25690 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9818

lemma sg25691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10267

lemma sg25692 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10293

lemma sg25693 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9819

lemma sg25694 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9788

lemma sg25695 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10268

lemma sg25696 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg8860 sg9088

lemma sg25697 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10264

lemma sg25698 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg8860 sg9089

lemma sg25699 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8727 sg9477

lemma sg25700 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10370

lemma sg25701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10294

lemma sg25702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9820

lemma sg25703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9541

lemma sg25704 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10371

lemma sg25705 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10295

lemma sg25706 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9821

lemma sg25707 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10270

lemma sg25708 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10372

lemma sg25709 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10296

lemma sg25710 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9822

lemma sg25711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9791

lemma sg25712 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10271

lemma sg25713 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg8861 sg9020

lemma sg25714 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9792

lemma sg25715 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10272

lemma sg25716 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9185

lemma sg25717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8861 sg9021

lemma sg25718 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg8350 sg10662

lemma sg25719 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9541

lemma sg25720 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10373

lemma sg25721 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10297

lemma sg25722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9823

lemma sg25723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9793

lemma sg25724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10273

lemma sg25725 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8861 sg9022

lemma sg25726 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10298

lemma sg25727 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9824

lemma sg25728 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9794

lemma sg25729 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10274

lemma sg25730 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9478

lemma sg25731 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg8861 sg9023

lemma sg25732 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9479

lemma sg25733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9479

lemma sg25734 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg8861 sg9024

lemma sg25735 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg8659 sg9697

lemma sg25736 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8525 sg10130

lemma sg25737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8530 sg10108

lemma sg25738 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8531 sg10102

lemma sg25739 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,5,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10102

end UniversalTensorSquare
end
end

end OAI
