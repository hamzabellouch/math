import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes21
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes24
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes44
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes41

namespace OAI

/-! Semigroup Nodes 72. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg29340 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg571 sg21238

lemma sg29341 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg571 sg21239

lemma sg29342 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg571 sg21240

lemma sg29343 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1718 sg18251

lemma sg29344 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1818 sg17134

lemma sg29345 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2182 sg15579

lemma sg29346 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2223 sg15546

lemma sg29347 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2668 sg15027

lemma sg29348 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2666 sg15032

lemma sg29349 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3513 sg14690

lemma sg29350 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg862 sg21165

lemma sg29351 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg862 sg21166

lemma sg29352 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg862 sg21167

lemma sg29353 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2183 sg15579

lemma sg29354 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2180 sg15581

lemma sg29355 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3868 sg14517

lemma sg29356 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2228 sg15535

lemma sg29357 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6930 sg11473

lemma sg29358 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5958 sg11837

lemma sg29359 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10342

lemma sg29360 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8357 sg10661

lemma sg29361 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3870 sg14515

lemma sg29362 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3867 sg14519

lemma sg29363 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6931 sg11473

lemma sg29364 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6928 sg11475

lemma sg29365 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10366

lemma sg29366 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8434 sg10289

lemma sg29367 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8651 sg9894

lemma sg29368 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6914 sg11478

lemma sg29369 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8122 sg11054

lemma sg29370 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10455

lemma sg29371 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10366

lemma sg29372 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8649 sg9899

lemma sg29373 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9240

lemma sg29374 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9231

lemma sg29375 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9926

lemma sg29376 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8650 sg9899

lemma sg29377 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10784

lemma sg29378 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10455

lemma sg29379 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg8648 sg9926

lemma sg29380 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1819 sg17134

lemma sg29381 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2184 sg15579

lemma sg29382 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2225 sg15543

lemma sg29383 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3869 sg14517

lemma sg29384 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2867 sg14859

lemma sg29385 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6933 sg11473

lemma sg29386 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5959 sg11837

lemma sg29387 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10338

lemma sg29388 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8359 sg10661

lemma sg29389 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2226 sg15543

lemma sg29390 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3871 sg14513

lemma sg29391 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3868 sg14518

lemma sg29392 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6934 sg11473

lemma sg29393 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6930 sg11474

lemma sg29394 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10343

lemma sg29395 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8438 sg10265

lemma sg29396 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8652 sg9894

lemma sg29397 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3870 sg14516

lemma sg29398 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6915 sg11478

lemma sg29399 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6912 sg11479

lemma sg29400 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10367

lemma sg29401 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9264

lemma sg29402 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8651 sg9895

lemma sg29403 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8123 sg11054

lemma sg29404 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10456

lemma sg29405 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10367

lemma sg29406 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9900

lemma sg29407 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9600

lemma sg29408 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8806 sg9240

lemma sg29409 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10785

lemma sg29410 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10456

lemma sg29411 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10367

lemma sg29412 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9927

lemma sg29413 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3886 sg14505

lemma sg29414 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3871 sg14514

lemma sg29415 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6916 sg11478

lemma sg29416 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8124 sg11054

lemma sg29417 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10344

lemma sg29418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9330

lemma sg29419 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8729 sg9541

lemma sg29420 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6986 sg11467

lemma sg29421 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8125 sg11054

lemma sg29422 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10368

lemma sg29423 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9265

lemma sg29424 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9896

lemma sg29425 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8730 sg9541

lemma sg29426 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10457

lemma sg29427 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10368

lemma sg29428 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10786

lemma sg29429 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10457

lemma sg29430 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9928

lemma sg29431 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10368

lemma sg29432 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9928

lemma sg29433 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10344

lemma sg29434 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5995 sg11830

lemma sg29435 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10458

lemma sg29436 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9266

lemma sg29437 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10787

lemma sg29438 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10458

lemma sg29439 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10369

lemma sg29440 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9929

lemma sg29441 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10369

lemma sg29442 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9929

lemma sg29443 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9902

lemma sg29444 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10345

lemma sg29445 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9903

lemma sg29446 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9903

lemma sg29447 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10346

lemma sg29448 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10341

lemma sg29449 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2193 sg15568

lemma sg29450 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2227 sg15543

lemma sg29451 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3872 sg14513

lemma sg29452 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3869 sg14518

lemma sg29453 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6946 sg11471

lemma sg29454 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6933 sg11474

lemma sg29455 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9243

lemma sg29456 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8476 sg10216

lemma sg29457 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8732 sg9540

lemma sg29458 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3901 sg14500

lemma sg29459 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4570 sg13500

lemma sg29460 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6972 sg11468

lemma sg29461 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8126 sg11054

lemma sg29462 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10347

lemma sg29463 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9243

lemma sg29464 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8652 sg9895

lemma sg29465 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6917 sg11478

lemma sg29466 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8127 sg11054

lemma sg29467 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10370

lemma sg29468 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9268

lemma sg29469 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9243

lemma sg29470 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9600

lemma sg29471 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10459

lemma sg29472 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10370

lemma sg29473 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10788

lemma sg29474 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10459

lemma sg29475 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9930

lemma sg29476 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10370

lemma sg29477 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9930

lemma sg29478 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8423 sg10347

lemma sg29479 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4571 sg13500

lemma sg29480 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6918 sg11478

lemma sg29481 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8128 sg11054

lemma sg29482 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10348

lemma sg29483 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9244

lemma sg29484 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9896

lemma sg29485 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9600

lemma sg29486 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6947 sg11472

lemma sg29487 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10460

lemma sg29488 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9269

lemma sg29489 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10789

lemma sg29490 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10460

lemma sg29491 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10371

lemma sg29492 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9931

lemma sg29493 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10371

lemma sg29494 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9931

lemma sg29495 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9905

lemma sg29496 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10348

lemma sg29497 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10372

lemma sg29498 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10372

lemma sg29499 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9932

lemma sg29500 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10372

lemma sg29501 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9932

lemma sg29502 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9906

lemma sg29503 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9906

lemma sg29504 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10349

lemma sg29505 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9245

lemma sg29506 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9246

lemma sg29507 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9246

lemma sg29508 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6919 sg11478

lemma sg29509 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6948 sg11472

lemma sg29510 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10461

lemma sg29511 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9247

lemma sg29512 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10790

lemma sg29513 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10461

lemma sg29514 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10373

lemma sg29515 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10373

lemma sg29516 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9933

lemma sg29517 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10373

lemma sg29518 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9933

lemma sg29519 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9907

lemma sg29520 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9907

lemma sg29521 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10350

lemma sg29522 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9247

lemma sg29523 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8434 sg10298

lemma sg29524 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9908

lemma sg29525 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9908

lemma sg29526 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10351

lemma sg29527 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8727 sg9545

lemma sg29528 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8728 sg9545

lemma sg29529 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8658 sg9779

lemma sg29530 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8384 sg10613

lemma sg29531 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8531 sg10130

lemma sg29532 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8532 sg10130

lemma sg29533 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,5,5,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8179 sg10866

lemma sg29534 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1319 sg20971

lemma sg29535 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1722 sg18249

lemma sg29536 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1825 sg17121

lemma sg29537 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2191 sg15569

lemma sg29538 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2224 sg15546

lemma sg29539 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2677 sg15016

lemma sg29540 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2175 sg15585

lemma sg29541 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3514 sg14688

lemma sg29542 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg867 sg21152

lemma sg29543 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg867 sg21153

lemma sg29544 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg867 sg21154

lemma sg29545 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1826 sg17121

lemma sg29546 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2192 sg15569

lemma sg29547 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2225 sg15546

lemma sg29548 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3879 sg14510

lemma sg29549 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2867 sg14860

lemma sg29550 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6968 sg11469

lemma sg29551 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5978 sg11834

lemma sg29552 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10342

lemma sg29553 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8369 sg10656

lemma sg29554 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2226 sg15546

lemma sg29555 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3871 sg14515

lemma sg29556 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3868 sg14519

lemma sg29557 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6969 sg11469

lemma sg29558 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6930 sg11475

lemma sg29559 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9272

lemma sg29560 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8480 sg10212

lemma sg29561 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8729 sg9542

lemma sg29562 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2669 sg15029

lemma sg29563 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6937 sg11473

lemma sg29564 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6931 sg11475

lemma sg29565 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8805 sg9242

lemma sg29566 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9272

lemma sg29567 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8651 sg9899

lemma sg29568 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6914 sg11479

lemma sg29569 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10462

lemma sg29570 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9233

lemma sg29571 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9909

lemma sg29572 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8720 sg9601

lemma sg29573 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8816 sg9234

lemma sg29574 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10791

lemma sg29575 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10462

lemma sg29576 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8345 sg10708

lemma sg29577 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,3,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9934

lemma sg29578 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2193 sg15569

lemma sg29579 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2227 sg15546

lemma sg29580 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3872 sg14515

lemma sg29581 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3869 sg14519

lemma sg29582 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6971 sg11469

lemma sg29583 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6933 sg11475

lemma sg29584 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10343

lemma sg29585 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8444 sg10265

lemma sg29586 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8732 sg9542

lemma sg29587 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3873 sg14513

lemma sg29588 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4570 sg13501

lemma sg29589 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6938 sg11473

lemma sg29590 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6934 sg11475

lemma sg29591 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8794 sg9273

lemma sg29592 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9331

lemma sg29593 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8652 sg9899

lemma sg29594 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6939 sg11473

lemma sg29595 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6915 sg11479

lemma sg29596 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10374

lemma sg29597 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9273

lemma sg29598 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9900

lemma sg29599 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8721 sg9601

lemma sg29600 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10463

lemma sg29601 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10374

lemma sg29602 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10792

lemma sg29603 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10463

lemma sg29604 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9935

lemma sg29605 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10374

lemma sg29606 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9935

lemma sg29607 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg8347 sg10707

lemma sg29608 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4571 sg13501

lemma sg29609 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6940 sg11473

lemma sg29610 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6916 sg11479

lemma sg29611 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10352

lemma sg29612 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9332

lemma sg29613 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8807 sg9241

lemma sg29614 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8722 sg9601

lemma sg29615 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5982 sg11834

lemma sg29616 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10464

lemma sg29617 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9274

lemma sg29618 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10793

lemma sg29619 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10464

lemma sg29620 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10375

lemma sg29621 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9936

lemma sg29622 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10375

lemma sg29623 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9936

lemma sg29624 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9911

lemma sg29625 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10352

lemma sg29626 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10376

lemma sg29627 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10376

lemma sg29628 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9937

lemma sg29629 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10376

lemma sg29630 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9937

lemma sg29631 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9912

lemma sg29632 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9912

lemma sg29633 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10353

lemma sg29634 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10345

lemma sg29635 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9602

lemma sg29636 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10346

lemma sg29637 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2236 sg15527

lemma sg29638 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3874 sg14513

lemma sg29639 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4573 sg13500

lemma sg29640 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6950 sg11471

lemma sg29641 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5986 sg11832

lemma sg29642 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8424 sg10347

lemma sg29643 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9331

lemma sg29644 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8732 sg9543

lemma sg29645 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4574 sg13500

lemma sg29646 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6941 sg11473

lemma sg29647 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6938 sg11474

lemma sg29648 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8420 sg10354

lemma sg29649 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9333

lemma sg29650 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8652 sg9900

lemma sg29651 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8733 sg9543

lemma sg29652 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6917 sg11479

lemma sg29653 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10465

lemma sg29654 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9276

lemma sg29655 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10794

lemma sg29656 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10465

lemma sg29657 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10377

lemma sg29658 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9938

lemma sg29659 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10377

lemma sg29660 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9938

lemma sg29661 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9913

lemma sg29662 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10354

lemma sg29663 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6942 sg11473

lemma sg29664 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6918 sg11479

lemma sg29665 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10466

lemma sg29666 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8791 sg9334

lemma sg29667 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10795

lemma sg29668 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10466

lemma sg29669 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10378

lemma sg29670 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10378

lemma sg29671 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9939

lemma sg29672 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10378

lemma sg29673 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9939

lemma sg29674 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9914

lemma sg29675 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9914

lemma sg29676 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10355

lemma sg29677 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10348

lemma sg29678 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9278

lemma sg29679 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9915

lemma sg29680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9915

lemma sg29681 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10356

lemma sg29682 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9603

lemma sg29683 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10349

lemma sg29684 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg8427 sg10346

lemma sg29685 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6919 sg11479

lemma sg29686 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10379

lemma sg29687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10379

lemma sg29688 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9940

lemma sg29689 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10379

lemma sg29690 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9940

lemma sg29691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9279

lemma sg29692 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9916

lemma sg29693 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9916

lemma sg29694 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10357

lemma sg29695 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9604

lemma sg29696 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10350

lemma sg29697 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9908

lemma sg29698 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8720 sg9605

lemma sg29699 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10351

lemma sg29700 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg8731 sg9545

lemma sg29701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8534 sg10130

lemma sg29702 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8535 sg10130

lemma sg29703 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3875 sg14513

lemma sg29704 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4575 sg13500

lemma sg29705 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6953 sg11471

lemma sg29706 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6012 sg11829

lemma sg29707 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8799 sg9256

lemma sg29708 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8793 sg9333

lemma sg29709 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9243

lemma sg29710 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8739 sg9537

lemma sg29711 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6954 sg11471

lemma sg29712 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6941 sg11474

lemma sg29713 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10467

lemma sg29714 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8800 sg9256

lemma sg29715 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8343 sg10796

lemma sg29716 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10467

lemma sg29717 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10380

lemma sg29718 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10380

lemma sg29719 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9941

lemma sg29720 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10380

lemma sg29721 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9941

lemma sg29722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9917

lemma sg29723 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9917

lemma sg29724 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10358

lemma sg29725 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9256

lemma sg29726 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6942 sg11474

lemma sg29727 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10381

lemma sg29728 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8417 sg10381

lemma sg29729 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9942

lemma sg29730 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8418 sg10381

lemma sg29731 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg8648 sg9942

lemma sg29732 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8795 sg9281

lemma sg29733 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg9918

lemma sg29734 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg8650 sg9918

lemma sg29735 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8423 sg10359

lemma sg29736 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9257

lemma sg29737 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg8803 sg9257

lemma sg29738 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8801 sg9258

lemma sg29739 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,7,6,6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8802 sg9258

end UniversalTensorSquare
end
end

end OAI
