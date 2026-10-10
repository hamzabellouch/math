import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes19

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9338 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6578

lemma sg9339 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6580

lemma sg9340 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6581

lemma sg9341 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6583

lemma sg9342 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg6584

lemma sg9343 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1397

lemma sg9344 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1790

lemma sg9345 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1398

lemma sg9346 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1285

lemma sg9347 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6587

lemma sg9348 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6589

lemma sg9349 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6591

lemma sg9350 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6592

lemma sg9351 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1498 sg1286

lemma sg9352 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1284

lemma sg9353 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6593

lemma sg9354 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6594

lemma sg9355 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6595

lemma sg9356 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6596

lemma sg9357 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg6597

lemma sg9358 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6598

lemma sg9359 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1 sg6599

lemma sg9360 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg1789

lemma sg9361 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6600

lemma sg9362 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5018

lemma sg9363 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5019

lemma sg9364 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,5,5,5] := by
  exact rowSquare_join (by decide) sg13 sg5020

lemma sg9365 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1399

lemma sg9366 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1791

lemma sg9367 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1790

lemma sg9368 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1003 sg1785

lemma sg9369 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1792

lemma sg9370 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1499 sg1285

lemma sg9371 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1790

lemma sg9372 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1377 sg1384

lemma sg9373 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1003 sg1787

lemma sg9374 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1790

lemma sg9375 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg1790

lemma sg9376 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1377 sg1385

lemma sg9377 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1501 sg1285

lemma sg9378 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5021

lemma sg9379 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5022

lemma sg9380 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg1890

lemma sg9381 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg939 sg1874

lemma sg9382 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1791

lemma sg9383 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg2309

lemma sg9384 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1006 sg1785

lemma sg9385 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1792

lemma sg9386 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1791

lemma sg9387 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg1786

lemma sg9388 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1791

lemma sg9389 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [7,7,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5025

lemma sg9390 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1402

lemma sg9391 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1403

lemma sg9392 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1404

lemma sg9393 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6606

lemma sg9394 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6607

lemma sg9395 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6608

lemma sg9396 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6609

lemma sg9397 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5027

lemma sg9398 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg6610

lemma sg9399 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5028

lemma sg9400 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg5029

lemma sg9401 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1405

lemma sg9402 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6611

lemma sg9403 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6612

lemma sg9404 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5030

lemma sg9405 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,5,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg6613

lemma sg9406 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6614

lemma sg9407 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5031

lemma sg9408 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,5,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5032

lemma sg9409 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,5,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5033

lemma sg9410 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1406

lemma sg9411 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6615

lemma sg9412 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6616

lemma sg9413 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6617

lemma sg9414 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5034

lemma sg9415 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5035

lemma sg9416 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5036

lemma sg9417 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,4,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5018

lemma sg9418 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,4,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5037

lemma sg9419 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,6,4,4] := by
  exact rowSquare_join (by decide) sg13 sg5038

lemma sg9420 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,7,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg1790

lemma sg9421 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,8,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5039

lemma sg9422 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,8,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg5025

lemma sg9423 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6618

lemma sg9424 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg5040

lemma sg9425 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg6619

lemma sg9426 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6620

lemma sg9427 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg6621

lemma sg9428 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg5041

lemma sg9429 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg6622

lemma sg9430 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg6623

lemma sg9431 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,4,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5042

lemma sg9432 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,4,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5043

lemma sg9433 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1407

lemma sg9434 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6624

lemma sg9435 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6625

lemma sg9436 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,5,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5044

lemma sg9437 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [9,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6626

lemma sg9438 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [10,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5046

lemma sg9439 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [10,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg6627

lemma sg9440 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [10,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5047

lemma sg9441 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1416

lemma sg9442 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1754

lemma sg9443 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1417

lemma sg9444 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1754

lemma sg9445 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1419

lemma sg9446 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1416

lemma sg9447 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1420

lemma sg9448 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1421

lemma sg9449 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1038 sg1754

lemma sg9450 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1422

lemma sg9451 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1039 sg1754

lemma sg9452 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1423

lemma sg9453 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1040 sg1754

lemma sg9454 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1424

lemma sg9455 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1755

lemma sg9456 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1755

lemma sg9457 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1425

lemma sg9458 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1416 sg1330

lemma sg9459 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1426

lemma sg9460 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1416 sg1331

lemma sg9461 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1756

lemma sg9462 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1416 sg1332

lemma sg9463 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg1758

lemma sg9464 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg1757

lemma sg9465 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1331

lemma sg9466 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1757

lemma sg9467 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1417 sg1332

lemma sg9468 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1758

lemma sg9469 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1427

lemma sg9470 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1428

lemma sg9471 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1429

lemma sg9472 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1045 sg1754

lemma sg9473 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1430

lemma sg9474 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1034 sg1758

lemma sg9475 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1431

lemma sg9476 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1432

lemma sg9477 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1433

lemma sg9478 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1418 sg1332

lemma sg9479 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1035 sg1758

lemma sg9480 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1047 sg1754

lemma sg9481 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1434

lemma sg9482 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8183

lemma sg9483 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8184

lemma sg9484 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8185

lemma sg9485 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8186

lemma sg9486 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8187

lemma sg9487 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8188

lemma sg9488 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1419 sg1332

lemma sg9489 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1037 sg1757

lemma sg9490 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8190

lemma sg9491 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8191

lemma sg9492 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1420

lemma sg9493 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1332 sg1421

lemma sg9494 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1048 sg1754

lemma sg9495 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1435

lemma sg9496 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1038 sg1755

lemma sg9497 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1422

lemma sg9498 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg889 sg1903

lemma sg9499 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1049 sg1754

lemma sg9500 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1436

lemma sg9501 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1039 sg1755

lemma sg9502 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1423

lemma sg9503 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1040 sg1755

lemma sg9504 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1424

lemma sg9505 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1417 sg1338

lemma sg9506 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1763

lemma sg9507 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1422 sg1332

lemma sg9508 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1437

lemma sg9509 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1041 sg1755

lemma sg9510 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1425

lemma sg9511 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1031 sg1764

lemma sg9512 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1426

lemma sg9513 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1417 sg1339

lemma sg9514 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1033 sg1764

lemma sg9515 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1423

lemma sg9516 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg1340

lemma sg9517 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1765

lemma sg9518 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1424

lemma sg9519 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1041 sg1756

lemma sg9520 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1425

lemma sg9521 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg1766

lemma sg9522 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1426

lemma sg9523 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1425

lemma sg9524 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1766

lemma sg9525 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1425

lemma sg9526 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1426

lemma sg9527 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg1332 sg1426

lemma sg9528 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1033 sg1767

lemma sg9529 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg891 sg1908

lemma sg9530 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg892 sg1908

lemma sg9531 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1050 sg1754

lemma sg9532 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1438

lemma sg9533 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1051 sg1754

lemma sg9534 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1439

lemma sg9535 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1052 sg1754

lemma sg9536 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1440

lemma sg9537 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1441

lemma sg9538 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1427 sg1332

lemma sg9539 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1042 sg1758

lemma sg9540 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1053 sg1754

lemma sg9541 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1442

lemma sg9542 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1054 sg1754

lemma sg9543 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1443

lemma sg9544 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8192

lemma sg9545 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1428 sg1332

lemma sg9546 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1444

lemma sg9547 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8193

lemma sg9548 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6563

lemma sg9549 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg6564

lemma sg9550 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2 sg6565

lemma sg9551 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1429

lemma sg9552 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8195

lemma sg9553 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6566

lemma sg9554 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg2 sg6567

lemma sg9555 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2 sg6568

lemma sg9556 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1055 sg1754

lemma sg9557 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1445

lemma sg9558 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1446

lemma sg9559 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8196

lemma sg9560 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8197

lemma sg9561 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8198

lemma sg9562 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1431

lemma sg9563 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8199

lemma sg9564 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8200

lemma sg9565 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8201

lemma sg9566 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8202

lemma sg9567 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg8203

lemma sg9568 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8204

lemma sg9569 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8205

lemma sg9570 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg0 sg8206

lemma sg9571 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1434

lemma sg9572 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5796

lemma sg9573 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8207

lemma sg9574 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5797

lemma sg9575 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5798

lemma sg9576 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg4 sg5799

lemma sg9577 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5800

lemma sg9578 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg4 sg5801

lemma sg9579 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg0 sg8208

lemma sg9580 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1056 sg1754

lemma sg9581 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1447

lemma sg9582 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1048 sg1755

lemma sg9583 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1435

lemma sg9584 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1422 sg1338

lemma sg9585 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1049 sg1755

lemma sg9586 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1436

lemma sg9587 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1520 sg1261

lemma sg9588 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg1348

lemma sg9589 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg1770

lemma sg9590 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1435

lemma sg9591 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1437

lemma sg9592 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1521 sg1261

lemma sg9593 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg5804

lemma sg9594 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg4063

lemma sg9595 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1448

lemma sg9596 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1449

lemma sg9597 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1450

lemma sg9598 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6569

lemma sg9599 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1438 sg1332

lemma sg9600 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1451

lemma sg9601 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1452

lemma sg9602 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6573

lemma sg9603 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg6574

lemma sg9604 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2 sg6575

lemma sg9605 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1439

lemma sg9606 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg6702

lemma sg9607 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5805

lemma sg9608 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5806

lemma sg9609 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5807

lemma sg9610 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg4 sg5808

lemma sg9611 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg6582

lemma sg9612 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2 sg6583

lemma sg9613 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg2 sg6584

lemma sg9614 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1453

lemma sg9615 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6586

lemma sg9616 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5809

lemma sg9617 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg6590

lemma sg9618 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2 sg6591

lemma sg9619 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2 sg6592

lemma sg9620 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5810

lemma sg9621 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5811

lemma sg9622 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5812

lemma sg9623 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5813

lemma sg9624 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg5814

lemma sg9625 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5800

lemma sg9626 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg5 sg5801

lemma sg9627 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5048

lemma sg9628 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5815

lemma sg9629 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5049

lemma sg9630 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5050

lemma sg9631 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg4 sg5816

lemma sg9632 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,5,5,5] := by
  exact rowSquare_join (by decide) sg2 sg6605

lemma sg9633 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,6,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1454

lemma sg9634 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8209

lemma sg9635 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg5817

lemma sg9636 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg5818

lemma sg9637 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg5802

lemma sg9638 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg5 sg5803

lemma sg9639 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg5804

lemma sg9640 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1056 sg1755

lemma sg9641 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1447

lemma sg9642 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,7,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1422 sg1348

lemma sg9643 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,7,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1038 sg1770

lemma sg9644 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,7,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5051

lemma sg9645 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,7,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg5819

lemma sg9646 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5052

lemma sg9647 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [7,7,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5053

lemma sg9648 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [8,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1448

lemma sg9649 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [8,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg5 sg5807

lemma sg9650 : RowSquare [6,4,2,2,1,1,1,1,1,1,1,1] [8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg5 sg5808

lemma sg9651 : RowSquare [6,4,3,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg374 sg2626

lemma sg9652 : RowSquare [6,4,3,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg370 sg2633

lemma sg9653 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1501

lemma sg9654 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1332 sg1502

lemma sg9655 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1,1] [6,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1507

lemma sg9656 : RowSquare [6,5,1,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1511

lemma sg9657 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1327 sg1371

lemma sg9658 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1371 sg1328

lemma sg9659 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1330

lemma sg9660 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1331

lemma sg9661 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg997 sg1758

lemma sg9662 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1755

lemma sg9663 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1007 sg1754

lemma sg9664 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1377

lemma sg9665 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1755

lemma sg9666 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1756

lemma sg9667 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1754

lemma sg9668 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1755

lemma sg9669 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1757

lemma sg9670 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1755

lemma sg9671 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1758

lemma sg9672 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1378

lemma sg9673 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg1756

lemma sg9674 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1379

lemma sg9675 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1756

lemma sg9676 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg1757

lemma sg9677 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1756

lemma sg9678 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg999 sg1758

lemma sg9679 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg1757

lemma sg9680 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1757

lemma sg9681 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg1758

lemma sg9682 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg1758

lemma sg9683 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1380

lemma sg9684 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8220

lemma sg9685 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1381

lemma sg9686 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8221

lemma sg9687 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg8222

lemma sg9688 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1382

lemma sg9689 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8223

lemma sg9690 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg8224

lemma sg9691 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1383

lemma sg9692 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8225

lemma sg9693 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1372 sg1331

lemma sg9694 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1002 sg1757

lemma sg9695 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8226

lemma sg9696 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1372 sg1332

lemma sg9697 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1002 sg1758

lemma sg9698 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1384

lemma sg9699 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1338

lemma sg9700 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1329 sg1373

lemma sg9701 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1014 sg1754

lemma sg9702 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1385

lemma sg9703 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1339

lemma sg9704 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8227

lemma sg9705 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1330 sg1373

lemma sg9706 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1386

lemma sg9707 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1340

lemma sg9708 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1375

lemma sg9709 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1373 sg1331

lemma sg9710 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1376

lemma sg9711 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1373 sg1332

lemma sg9712 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1003 sg1758

lemma sg9713 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1387

lemma sg9714 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1378

lemma sg9715 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8228

lemma sg9716 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1330 sg1374

lemma sg9717 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1328 sg1379

lemma sg9718 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg8229

lemma sg9719 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1375

lemma sg9720 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1331 sg1374

lemma sg9721 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1376

lemma sg9722 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1374 sg1332

lemma sg9723 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1005 sg1757

lemma sg9724 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1375

lemma sg9725 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1376

lemma sg9726 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1375

lemma sg9727 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1332 sg1376

lemma sg9728 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1015 sg1754

lemma sg9729 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1006 sg1755

lemma sg9730 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg1763

lemma sg9731 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1016 sg1754

lemma sg9732 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1327 sg1388

lemma sg9733 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1007 sg1755

lemma sg9734 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1329 sg1377

lemma sg9735 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg998 sg1764

lemma sg9736 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1008 sg1755

lemma sg9737 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg1765

end UniversalTensorSquare
end
end

end OAI
