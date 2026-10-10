import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes25
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes9

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11339 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1766

lemma sg11340 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg890 sg2275

lemma sg11341 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1330 sg1767

lemma sg11342 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1331 sg1766

lemma sg11343 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg890 sg2277

lemma sg11344 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg1332 sg1766

lemma sg11345 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1331 sg1767

lemma sg11346 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg891 sg2276

lemma sg11347 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1767

lemma sg11348 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg892 sg2277

lemma sg11349 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5842

lemma sg11350 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5849

lemma sg11351 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [6,6,6,5] := by
  exact rowSquare_join (by decide) sg13 sg5852

lemma sg11352 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5869

lemma sg11353 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5871

lemma sg11354 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5873

lemma sg11355 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,6,5,5] := by
  exact rowSquare_join (by decide) sg13 sg5874

lemma sg11356 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5878

lemma sg11357 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg5880

lemma sg11358 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,7,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5881

lemma sg11359 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,1] := by
  exact rowSquare_join (by decide) sg13 sg5882

lemma sg11360 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,7,5,4] := by
  exact rowSquare_join (by decide) sg13 sg5883

lemma sg11361 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5888

lemma sg11362 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [9,8,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1365 sg1763

lemma sg11363 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [9,9,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg5889

lemma sg11364 : RowSquare [6,6,2,2,2,2,2,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7812

lemma sg11365 : RowSquare [6,6,2,2,2,2,2,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7813

lemma sg11366 : RowSquare [6,6,2,2,2,2,2,1] [5,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7816

lemma sg11367 : RowSquare [6,6,2,2,2,2,2,1] [5,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7817

lemma sg11368 : RowSquare [6,6,2,2,2,2,2,1] [5,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7818

lemma sg11369 : RowSquare [6,6,2,2,2,2,2,1] [5,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7819

lemma sg11370 : RowSquare [6,6,2,2,2,2,2,1] [5,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7820

lemma sg11371 : RowSquare [6,6,2,2,2,2,2,1] [5,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg7821

lemma sg11372 : RowSquare [6,6,2,2,2,2,2,1] [5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7823

lemma sg11373 : RowSquare [6,6,2,2,2,2,2,1] [5,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7824

lemma sg11374 : RowSquare [6,6,2,2,2,2,2,1] [5,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7825

lemma sg11375 : RowSquare [6,6,2,2,2,2,2,1] [5,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7826

lemma sg11376 : RowSquare [6,6,2,2,2,2,2,1] [5,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7827

lemma sg11377 : RowSquare [6,6,2,2,2,2,2,1] [5,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg7828

lemma sg11378 : RowSquare [6,6,2,2,2,2,2,1] [5,4,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7831

lemma sg11379 : RowSquare [6,6,2,2,2,2,2,1] [5,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7832

lemma sg11380 : RowSquare [6,6,2,2,2,2,2,1] [5,4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7833

lemma sg11381 : RowSquare [6,6,2,2,2,2,2,1] [5,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7834

lemma sg11382 : RowSquare [6,6,2,2,2,2,2,1] [5,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg7835

lemma sg11383 : RowSquare [6,6,2,2,2,2,2,1] [5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7837

lemma sg11384 : RowSquare [6,6,2,2,2,2,2,1] [5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7840

lemma sg11385 : RowSquare [6,6,2,2,2,2,2,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7822

lemma sg11386 : RowSquare [6,6,2,2,2,2,2,1] [6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7841

lemma sg11387 : RowSquare [6,6,2,2,2,2,2,1] [6,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7824

lemma sg11388 : RowSquare [6,6,2,2,2,2,2,1] [6,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7825

lemma sg11389 : RowSquare [6,6,2,2,2,2,2,1] [6,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7826

lemma sg11390 : RowSquare [6,6,2,2,2,2,2,1] [6,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7827

lemma sg11391 : RowSquare [6,6,2,2,2,2,2,1] [6,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg7828

lemma sg11392 : RowSquare [6,6,2,2,2,2,2,1] [6,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7842

lemma sg11393 : RowSquare [6,6,2,2,2,2,2,1] [6,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7843

lemma sg11394 : RowSquare [6,6,2,2,2,2,2,1] [6,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7844

lemma sg11395 : RowSquare [6,6,2,2,2,2,2,1] [6,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7845

lemma sg11396 : RowSquare [6,6,2,2,2,2,2,1] [6,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg7846

lemma sg11397 : RowSquare [6,6,2,2,2,2,2,1] [6,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7853

lemma sg11398 : RowSquare [6,6,2,2,2,2,2,1] [6,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7854

lemma sg11399 : RowSquare [6,6,2,2,2,2,2,1] [6,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7855

lemma sg11400 : RowSquare [6,6,2,2,2,2,2,1] [6,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7856

lemma sg11401 : RowSquare [6,6,2,2,2,2,2,1] [6,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg7857

lemma sg11402 : RowSquare [6,6,2,2,2,2,2,1] [6,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7837

lemma sg11403 : RowSquare [6,6,2,2,2,2,2,1] [6,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg7839

lemma sg11404 : RowSquare [6,6,2,2,2,2,2,1] [6,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7840

lemma sg11405 : RowSquare [6,6,2,2,2,2,2,1] [6,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7848

lemma sg11406 : RowSquare [6,6,2,2,2,2,2,1] [6,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7849

lemma sg11407 : RowSquare [6,6,2,2,2,2,2,1] [6,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7850

lemma sg11408 : RowSquare [6,6,2,2,2,2,2,1] [6,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg7851

lemma sg11409 : RowSquare [6,6,2,2,2,2,2,1] [6,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7852

lemma sg11410 : RowSquare [6,6,2,2,2,2,2,1] [6,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg7858

lemma sg11411 : RowSquare [6,6,2,2,2,2,2,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7841

lemma sg11412 : RowSquare [6,6,2,2,2,2,2,1] [7,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7842

lemma sg11413 : RowSquare [6,6,2,2,2,2,2,1] [7,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7843

lemma sg11414 : RowSquare [6,6,2,2,2,2,2,1] [7,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7844

lemma sg11415 : RowSquare [6,6,2,2,2,2,2,1] [7,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7845

lemma sg11416 : RowSquare [6,6,2,2,2,2,2,1] [7,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg7846

lemma sg11417 : RowSquare [6,6,2,2,2,2,2,1] [7,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7854

lemma sg11418 : RowSquare [6,6,2,2,2,2,2,1] [7,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7855

lemma sg11419 : RowSquare [6,6,2,2,2,2,2,1] [7,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg7856

lemma sg11420 : RowSquare [6,6,2,2,2,2,2,1] [7,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg7857

lemma sg11421 : RowSquare [6,6,2,2,2,2,2,1] [8,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7854

lemma sg11422 : RowSquare [6,6,2,2,2,2,2,1] [8,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7855

lemma sg11423 : RowSquare [6,6,2,2,2,2,2,1] [8,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg7856

lemma sg11424 : RowSquare [6,6,2,2,2,2,2,1] [8,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg7857

lemma sg11425 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg997 sg2251

lemma sg11426 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg2251

lemma sg11427 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg2251

lemma sg11428 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg2251

lemma sg11429 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1001 sg2251

lemma sg11430 : RowSquare [7,5,1,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1002 sg2251

lemma sg11431 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg2702

lemma sg11432 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg2702

lemma sg11433 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2702

lemma sg11434 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2702

lemma sg11435 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg915 sg2251

lemma sg11436 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg910 sg2256

lemma sg11437 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg2707

lemma sg11438 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg2708

lemma sg11439 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg587 sg2708

lemma sg11440 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg2702

lemma sg11441 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg920 sg2251

lemma sg11442 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg2702

lemma sg11443 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg921 sg2251

lemma sg11444 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg588 sg2708

lemma sg11445 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg2713

lemma sg11446 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg589 sg2708

lemma sg11447 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg2706

lemma sg11448 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg915 sg2256

lemma sg11449 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg2702

lemma sg11450 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg931 sg2251

lemma sg11451 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,5,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg923 sg2257

lemma sg11452 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg930 sg2254

lemma sg11453 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg939 sg2251

lemma sg11454 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg931 sg2253

lemma sg11455 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg910 sg2269

lemma sg11456 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg920 sg2261

lemma sg11457 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg932 sg2253

lemma sg11458 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg931 sg2254

lemma sg11459 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg6017

lemma sg11460 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg932 sg2254

lemma sg11461 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg6018

lemma sg11462 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [6,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg6019

lemma sg11463 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg939 sg2253

lemma sg11464 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [7,7,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg939 sg2254

lemma sg11465 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [7,7,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg6020

lemma sg11466 : RowSquare [7,5,2,1,1,1,1,1,1,1,1,1] [8,8,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg6020

lemma sg11467 : RowSquare [7,5,3,2,1,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg132 sg4160

lemma sg11468 : RowSquare [7,5,3,2,1,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg133 sg4160

lemma sg11469 : RowSquare [7,5,3,2,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg134 sg4160

lemma sg11470 : RowSquare [7,5,3,2,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg479 sg2702

lemma sg11471 : RowSquare [7,5,3,2,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg135 sg4160

lemma sg11472 : RowSquare [7,5,3,2,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg132 sg4161

lemma sg11473 : RowSquare [7,5,3,2,1,1,1,1,1,1] [5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg136 sg4160

lemma sg11474 : RowSquare [7,5,3,2,1,1,1,1,1,1] [5,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg133 sg4161

lemma sg11475 : RowSquare [7,5,3,2,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg134 sg4161

lemma sg11476 : RowSquare [7,5,3,2,1,1,1,1,1,1] [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg137 sg4160

lemma sg11477 : RowSquare [7,5,3,2,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg135 sg4161

lemma sg11478 : RowSquare [7,5,3,2,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg139 sg4160

lemma sg11479 : RowSquare [7,5,3,2,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg136 sg4161

lemma sg11480 : RowSquare [7,5,3,2,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg137 sg4161

lemma sg11481 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg888 sg2251

lemma sg11482 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg2251

lemma sg11483 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg890 sg2251

lemma sg11484 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg891 sg2251

lemma sg11485 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg2251

lemma sg11486 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg893 sg2251

lemma sg11487 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg894 sg2251

lemma sg11488 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg895 sg2251

lemma sg11489 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg896 sg2251

lemma sg11490 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg888 sg2255

lemma sg11491 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg2252

lemma sg11492 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg888 sg2256

lemma sg11493 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg897 sg2251

lemma sg11494 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg898 sg2251

lemma sg11495 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg899 sg2251

lemma sg11496 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg889 sg2256

lemma sg11497 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg890 sg2254

lemma sg11498 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg891 sg2254

lemma sg11499 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg2254

lemma sg11500 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg891 sg2255

lemma sg11501 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg2255

lemma sg11502 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg892 sg2256

lemma sg11503 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg902 sg2251

lemma sg11504 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg903 sg2251

lemma sg11505 : RowSquare [7,6,1,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg909 sg2251

lemma sg11506 : RowSquare [7,6,2,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg525 sg2702

lemma sg11507 : RowSquare [7,6,2,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg825 sg2251

lemma sg11508 : RowSquare [7,6,2,2,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg459 sg2702

lemma sg11509 : RowSquare [7,6,2,2,2,2,1,1] [5,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10889

lemma sg11510 : RowSquare [7,6,2,2,2,2,1,1] [5,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10890

lemma sg11511 : RowSquare [7,6,2,2,2,2,1,1] [5,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10891

lemma sg11512 : RowSquare [7,6,2,2,2,2,1,1] [5,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10892

lemma sg11513 : RowSquare [7,6,2,2,2,2,1,1] [5,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10893

lemma sg11514 : RowSquare [7,6,2,2,2,2,1,1] [5,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg10894

lemma sg11515 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10895

lemma sg11516 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10896

lemma sg11517 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10897

lemma sg11518 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg10898

lemma sg11519 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10899

lemma sg11520 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10900

lemma sg11521 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10901

lemma sg11522 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg10902

lemma sg11523 : RowSquare [7,6,2,2,2,2,1,1] [5,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10903

lemma sg11524 : RowSquare [7,6,2,2,2,2,1,1] [5,4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10904

lemma sg11525 : RowSquare [7,6,2,2,2,2,1,1] [5,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10905

lemma sg11526 : RowSquare [7,6,2,2,2,2,1,1] [5,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10906

lemma sg11527 : RowSquare [7,6,2,2,2,2,1,1] [5,4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10907

lemma sg11528 : RowSquare [7,6,2,2,2,2,1,1] [5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10908

lemma sg11529 : RowSquare [7,6,2,2,2,2,1,1] [5,4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10909

lemma sg11530 : RowSquare [7,6,2,2,2,2,1,1] [6,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg10910

lemma sg11532 : RowSquare [7,6,3,2,2,2,1] [2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1221 sg1615

lemma sg11533 : RowSquare [7,6,3,2,2,2,1] [2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1219 sg1614

lemma sg11534 : RowSquare [7,6,3,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1219 sg1612

lemma sg11535 : RowSquare [8,3,2,2,2,2,2,1,1] [5,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg358 sg3279

lemma sg11536 : RowSquare [8,3,2,2,2,2,2,2] [6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg579 sg2550

lemma sg11537 : RowSquare [8,6,1,1,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg262 sg3521

lemma sg11538 : RowSquare [8,6,1,1,1,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg263 sg3521

lemma sg11539 : RowSquare [8,6,1,1,1,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg265 sg3521

lemma sg11540 : RowSquare [8,6,2,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg3521

lemma sg11541 : RowSquare [8,6,2,1,1,1,1,1,1,1] [5,4,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg240 sg3521

lemma sg11542 : RowSquare [8,6,2,1,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg3521

lemma sg11543 : RowSquare [8,6,2,1,1,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg111 sg4345

lemma sg11544 : RowSquare [9,3,2,2,2,2,2,1] [4,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg4805

lemma sg11545 : RowSquare [9,3,2,2,2,2,2,1] [5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg356 sg3209

lemma sg11546 : RowSquare [9,3,2,2,2,2,2,1] [5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg4807

lemma sg11547 : RowSquare [9,3,2,2,2,2,2,1] [6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg165 sg3968

lemma sg11548 : RowSquare [9,4,2,2,2,2,2] [5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg295 sg3209

lemma sg11549 : RowSquare [10,3,2,2,2,2,1,1] [4,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg4741

lemma sg11550 : RowSquare [10,3,2,2,2,2,1,1] [5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg74 sg4748

lemma sg11551 : RowSquare [10,3,2,2,2,2,1,1] [5,5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg74 sg4749

lemma sg11552 : RowSquare [10,3,2,2,2,2,1,1] [5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg4750

lemma sg11553 : RowSquare [10,3,2,2,2,2,2] [6,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg165 sg3870

lemma sg11554 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6] := by
  exact rowSquare_join (by decide) sg390 sg4543

lemma sg11555 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1914 sg1977

lemma sg11556 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg1914 sg1978

lemma sg11557 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1970 sg1925

lemma sg11558 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1105 sg3102

lemma sg11559 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1970 sg1926

lemma sg11560 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1914 sg1979

lemma sg11561 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1914 sg1980

lemma sg11562 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,3] := by
  exact rowSquare_join (by decide) sg1532 sg2452

lemma sg11563 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg1914 sg1981

lemma sg11564 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg1916 sg1977

lemma sg11565 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1915 sg1978

lemma sg11566 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg1916 sg1978

lemma sg11567 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg1971 sg1926

lemma sg11568 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,5] := by
  exact rowSquare_join (by decide) sg1539 sg2439

lemma sg11569 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1455 sg2479

lemma sg11570 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1915 sg1979

lemma sg11571 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg1916 sg1979

lemma sg11572 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1915 sg1980

lemma sg11573 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg1916 sg1980

lemma sg11574 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,2,2,1] := by
  exact rowSquare_join (by decide) sg1917 sg1979

lemma sg11575 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1915 sg1981

lemma sg11576 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,2] := by
  exact rowSquare_join (by decide) sg1916 sg1981

lemma sg11577 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,1] := by
  exact rowSquare_join (by decide) sg1925 sg1973

lemma sg11578 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,5,5] := by
  exact rowSquare_join (by decide) sg1926 sg1973

lemma sg11579 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg1844 sg2002

lemma sg11580 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1844 sg2003

lemma sg11581 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1914 sg1984

lemma sg11582 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1927 sg1970

lemma sg11583 : RowSquare [3,3,3,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4] := by
  exact rowSquare_join (by decide) sg1926 sg1976

lemma sg11584 : RowSquare [3,3,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1532 sg2432

lemma sg11585 : RowSquare [3,3,3,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg1061 sg3151

lemma sg11586 : RowSquare [3,3,3,3,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg1914 sg1970

lemma sg11587 : RowSquare [3,3,3,3,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1916 sg1970

lemma sg11588 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1] [5,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg636 sg3657

lemma sg11589 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1] [6,4,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1300 sg2433

lemma sg11590 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1] [6,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1062 sg2838

lemma sg11591 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1] [6,5,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg872 sg3152

lemma sg11592 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1] [6,6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1063 sg2838

lemma sg11593 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1] [6,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1735 sg1975

lemma sg11594 : RowSquare [3,3,3,3,3,2,1,1,1,1,1,1,1] [7,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1810 sg1914

lemma sg11595 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1957 sg1924

lemma sg11596 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg1994

lemma sg11597 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg1980

lemma sg11598 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg3154

lemma sg11599 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1954 sg1927

lemma sg11600 : RowSquare [4,3,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1891 sg1997

lemma sg11601 : RowSquare [4,3,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg3152

lemma sg11602 : RowSquare [4,3,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6] := by
  exact rowSquare_join (by decide) sg390 sg4539

lemma sg11603 : RowSquare [4,3,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg1976

lemma sg11604 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1517 sg2405

lemma sg11605 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1517 sg2406

lemma sg11606 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1517 sg2407

lemma sg11607 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1518 sg2406

lemma sg11608 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1518 sg2407

lemma sg11609 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1519 sg2407

lemma sg11610 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1520 sg2405

lemma sg11611 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1520 sg2406

lemma sg11612 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg2407

lemma sg11613 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg3148

lemma sg11614 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1032 sg3149

lemma sg11615 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg1033 sg3149

lemma sg11616 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1521 sg2405

lemma sg11617 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,2,2] := by
  exact rowSquare_join (by decide) sg1521 sg2406

lemma sg11618 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1521 sg2407

lemma sg11619 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1522 sg2405

lemma sg11620 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1523 sg2405

lemma sg11621 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg1522 sg2406

lemma sg11622 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg1522 sg2407

lemma sg11623 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg1523 sg2406

lemma sg11624 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg1523 sg2407

lemma sg11625 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1901 sg1954

lemma sg11626 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg1955

lemma sg11627 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg1956

lemma sg11628 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1902 sg1955

lemma sg11629 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg1956

lemma sg11630 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1901 sg1957

lemma sg11631 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg1955

lemma sg11632 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1902 sg1957

lemma sg11633 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg1956

lemma sg11634 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg1958

lemma sg11635 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1904 sg1954

lemma sg11636 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1902 sg1958

lemma sg11637 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1904 sg1956

lemma sg11638 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1905 sg1955

lemma sg11639 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1905 sg1956

lemma sg11640 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4] := by
  exact rowSquare_join (by decide) sg1519 sg2413

lemma sg11641 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg1959

lemma sg11642 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1954 sg1906

lemma sg11643 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg1960

lemma sg11644 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg1959

lemma sg11645 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,2,2] := by
  exact rowSquare_join (by decide) sg1955 sg1906

lemma sg11646 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg1906 sg1956

lemma sg11647 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg1960

lemma sg11648 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg1955 sg1907

lemma sg11649 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1956 sg1907

lemma sg11650 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1955 sg1908

lemma sg11651 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1956 sg1908

lemma sg11652 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1903 sg1957

lemma sg11653 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg1961

lemma sg11654 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1904 sg1957

lemma sg11655 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1902 sg1961

lemma sg11656 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg2413

lemma sg11657 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg1962

lemma sg11658 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1904 sg1958

lemma sg11659 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg1963

lemma sg11660 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg1962

lemma sg11661 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,2,2] := by
  exact rowSquare_join (by decide) sg1905 sg1958

lemma sg11662 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,3,3,1] := by
  exact rowSquare_join (by decide) sg1521 sg2413

lemma sg11663 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg1902 sg1963

lemma sg11664 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,1] := by
  exact rowSquare_join (by decide) sg1518 sg2419

lemma sg11665 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,3] := by
  exact rowSquare_join (by decide) sg1519 sg2419

lemma sg11666 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1904 sg1959

lemma sg11667 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg1906 sg1958

lemma sg11668 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1904 sg1960

lemma sg11669 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,3,2,1] := by
  exact rowSquare_join (by decide) sg1905 sg1959

lemma sg11670 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg1519 sg2420

lemma sg11671 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg1905 sg1960

lemma sg11672 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg1519 sg2421

lemma sg11673 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg1961

lemma sg11674 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1520 sg2417

lemma sg11675 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg1962

lemma sg11676 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1904 sg1961

lemma sg11677 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg1963

lemma sg11678 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg2419

lemma sg11679 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1905 sg1961

lemma sg11680 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1038 sg3149

lemma sg11681 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1904 sg1962

lemma sg11682 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1906 sg1961

lemma sg11683 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1904 sg1963

lemma sg11684 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1905 sg1962

lemma sg11685 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg1527 sg2407

lemma sg11686 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1905 sg1963

lemma sg11687 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg1033 sg3150

lemma sg11688 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1520 sg2422

lemma sg11689 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,2,2,1] := by
  exact rowSquare_join (by decide) sg1906 sg1962

lemma sg11690 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,3,1,1] := by
  exact rowSquare_join (by decide) sg1906 sg1963

lemma sg11691 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,3,2] := by
  exact rowSquare_join (by decide) sg1907 sg1962

lemma sg11692 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,4,1] := by
  exact rowSquare_join (by decide) sg1907 sg1963

lemma sg11693 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5] := by
  exact rowSquare_join (by decide) sg1908 sg1963

lemma sg11694 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1901 sg1964

lemma sg11695 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1811 sg1998

lemma sg11696 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1903 sg1964

lemma sg11697 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1901 sg1965

lemma sg11698 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1811 sg1999

lemma sg11699 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg1902 sg1965

lemma sg11700 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1909 sg1956

lemma sg11701 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1901 sg1966

lemma sg11702 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1811 sg2000

lemma sg11703 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1811 sg2001

lemma sg11704 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1957 sg1911

lemma sg11705 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1904 sg1967

lemma sg11706 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1961 sg1910

lemma sg11707 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg1906 sg1967

lemma sg11708 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1957 sg1912

lemma sg11709 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1903 sg1968

lemma sg11710 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1961 sg1912

lemma sg11711 : RowSquare [4,4,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1905 sg1968

lemma sg11712 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg1523 sg2395

lemma sg11713 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,6,6] := by
  exact rowSquare_join (by decide) sg390 sg4526

lemma sg11714 : RowSquare [4,4,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1520 sg2399

lemma sg11715 : RowSquare [4,4,3,2,2,2,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg4506

lemma sg11716 : RowSquare [4,4,3,2,2,2,1,1,1,1,1,1,1] [5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg4508

lemma sg11717 : RowSquare [4,4,3,2,2,2,1,1,1,1,1,1,1] [6,6,6,6] := by
  exact rowSquare_join (by decide) sg390 sg4419

lemma sg11718 : RowSquare [5,3,3,3,2,1,1,1,1,1,1,1,1] [6,6,6,6] := by
  exact rowSquare_join (by decide) sg390 sg4405

lemma sg11719 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [6,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1517 sg2372

lemma sg11720 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1520 sg2372

lemma sg11721 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [6,6,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1521 sg2372

lemma sg11722 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,5,5,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1954 sg1878

lemma sg11723 : RowSquare [5,4,2,2,1,1,1,1,1,1,1,1,1,1,1] [7,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg1878 sg1958

lemma sg11724 : RowSquare [5,4,2,2,2,2,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1875 sg1811

lemma sg11725 : RowSquare [5,4,2,2,2,2,1,1,1,1,1,1,1] [5,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1417 sg2291

lemma sg11726 : RowSquare [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg3115

lemma sg11727 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg3650

lemma sg11728 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1372 sg2288

lemma sg11729 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg911 sg2958

lemma sg11730 : RowSquare [5,5,2,2,2,1,1,1,1,1,1,1,1] [5,5,5,5,4] := by
  exact rowSquare_join (by decide) sg1001 sg2784

lemma sg11731 : RowSquare [5,5,2,2,2,2,2,2,1,1] [8,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg411 sg3999

lemma sg11732 : RowSquare [5,5,2,2,2,2,2,2,1,1] [8,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg412 sg3999

lemma sg11733 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg1874

lemma sg11734 : RowSquare [6,5,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1754 sg1878

lemma sg11735 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg998 sg2633

lemma sg11736 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg2633

lemma sg11737 : RowSquare [6,5,3,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1002 sg2633

lemma sg11738 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1754 sg1872

lemma sg11739 : RowSquare [6,6,2,2,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1754 sg1754

end UniversalTensorSquare
end
end

end OAI
