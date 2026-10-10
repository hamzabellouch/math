import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes13
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes14

namespace OAI

/-! Semigroup Nodes 17. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7334 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6093

lemma sg7335 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6094

lemma sg7336 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg6095

lemma sg7337 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg620 sg1331

lemma sg7338 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6096

lemma sg7339 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg0 sg6097

lemma sg7340 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg621 sg1329

lemma sg7341 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1038

lemma sg7342 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg614 sg1338

lemma sg7343 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg378 sg1755

lemma sg7344 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg622 sg1329

lemma sg7345 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1039

lemma sg7346 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1031 sg897

lemma sg7347 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1040

lemma sg7348 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1340

lemma sg7349 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1032 sg897

lemma sg7350 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1038 sg892

lemma sg7351 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg623 sg1329

lemma sg7352 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1041

lemma sg7353 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg898

lemma sg7354 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg1339

lemma sg7355 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1031 sg899

lemma sg7356 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1032 sg898

lemma sg7357 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1033 sg898

lemma sg7358 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg899

lemma sg7359 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1033 sg899

lemma sg7360 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg623 sg1330

lemma sg7361 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg890 sg1041

lemma sg7362 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg623 sg1332

lemma sg7363 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg891 sg1041

lemma sg7364 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg892 sg1041

lemma sg7365 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg373 sg1767

lemma sg7366 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6098

lemma sg7367 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6099

lemma sg7368 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6100

lemma sg7369 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg5197

lemma sg7370 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6101

lemma sg7371 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg5198

lemma sg7372 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5199

lemma sg7373 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg624 sg1332

lemma sg7374 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6102

lemma sg7375 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg5200

lemma sg7376 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6103

lemma sg7377 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5341

lemma sg7378 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg5201

lemma sg7379 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5342

lemma sg7380 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6104

lemma sg7381 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2 sg5202

lemma sg7382 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2 sg5203

lemma sg7383 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5343

lemma sg7384 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6105

lemma sg7385 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4587

lemma sg7386 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6106

lemma sg7387 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4588

lemma sg7388 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4589

lemma sg7389 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg4 sg4590

lemma sg7390 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5208

lemma sg7391 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2 sg5209

lemma sg7392 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg628 sg1328

lemma sg7393 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6107

lemma sg7394 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6108

lemma sg7395 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6109

lemma sg7396 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4591

lemma sg7397 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6110

lemma sg7398 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6111

lemma sg7399 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6112

lemma sg7400 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg6113

lemma sg7401 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6114

lemma sg7402 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4592

lemma sg7403 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4593

lemma sg7404 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4594

lemma sg7405 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg4 sg4595

lemma sg7406 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg6115

lemma sg7407 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4596

lemma sg7408 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4597

lemma sg7409 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4598

lemma sg7410 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg4 sg4599

lemma sg7411 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,5,5,4] := by
  exact rowSquare_join (by decide) sg4 sg4600

lemma sg7412 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg1755

lemma sg7413 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg628 sg1329

lemma sg7414 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1048

lemma sg7415 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg614 sg1348

lemma sg7416 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1038 sg897

lemma sg7417 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg1049

lemma sg7418 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4601

lemma sg7419 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4602

lemma sg7420 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1032 sg902

lemma sg7421 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,3,3,2] := by
  exact rowSquare_join (by decide) sg1033 sg902

lemma sg7422 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4603

lemma sg7423 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4604

lemma sg7424 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,4,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4605

lemma sg7425 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,4,3,1] := by
  exact rowSquare_join (by decide) sg4 sg4606

lemma sg7426 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,4,4] := by
  exact rowSquare_join (by decide) sg1040 sg899

lemma sg7427 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4607

lemma sg7428 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,5,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4608

lemma sg7429 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,5,3] := by
  exact rowSquare_join (by decide) sg4 sg4609

lemma sg7430 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,6,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4610

lemma sg7431 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [6,6,6,2] := by
  exact rowSquare_join (by decide) sg4 sg4611

lemma sg7432 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5344

lemma sg7433 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5345

lemma sg7434 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg5212

lemma sg7435 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5346

lemma sg7436 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4612

lemma sg7437 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg5216

lemma sg7438 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg2 sg5217

lemma sg7439 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2 sg5218

lemma sg7440 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6116

lemma sg7441 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg5219

lemma sg7442 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4613

lemma sg7443 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4614

lemma sg7444 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg4588

lemma sg7445 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg5 sg4589

lemma sg7446 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg5 sg4590

lemma sg7447 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3797

lemma sg7448 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4615

lemma sg7449 : RowSquare [6,4,2,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6117

lemma sg7450 : RowSquare [6,4,2,2,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1754

lemma sg7451 : RowSquare [6,4,2,2,1,1,1,1,1,1] [3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg1758

lemma sg7452 : RowSquare [6,4,2,2,1,1,1,1,1,1] [4,4,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg332 sg1755

lemma sg7453 : RowSquare [6,4,2,2,1,1,1,1,1,1] [4,4,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg334 sg1756

lemma sg7454 : RowSquare [6,4,2,2,1,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg4063

lemma sg7455 : RowSquare [6,4,2,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg342 sg1754

lemma sg7456 : RowSquare [6,4,2,2,1,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg4064

lemma sg7457 : RowSquare [6,4,2,2,1,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg4065

lemma sg7458 : RowSquare [6,4,2,2,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6124

lemma sg7459 : RowSquare [6,4,2,2,1,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg4071

lemma sg7460 : RowSquare [6,4,2,2,1,1,1,1,1,1] [8,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6125

lemma sg7461 : RowSquare [6,4,2,2,1,1,1,1,1,1] [8,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5356

lemma sg7462 : RowSquare [6,4,2,2,2,2,1,1] [4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4078

lemma sg7463 : RowSquare [6,4,2,2,2,2,1,1] [4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg878 sg808

lemma sg7464 : RowSquare [6,4,2,2,2,2,1,1] [4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg960 sg762

lemma sg7465 : RowSquare [6,4,2,2,2,2,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg4063

lemma sg7466 : RowSquare [6,4,2,2,2,2,1,1] [5,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg4071

lemma sg7467 : RowSquare [6,4,2,2,2,2,1,1] [5,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4080

lemma sg7468 : RowSquare [6,4,2,2,2,2,1,1] [5,4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg4072

lemma sg7469 : RowSquare [6,4,2,2,2,2,1,1] [5,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg4073

lemma sg7470 : RowSquare [6,4,2,2,2,2,1,1] [5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg4074

lemma sg7471 : RowSquare [6,4,2,2,2,2,1,1] [5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg4081

lemma sg7472 : RowSquare [6,4,2,2,2,2,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg958 sg765

lemma sg7473 : RowSquare [6,4,2,2,2,2,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg4064

lemma sg7474 : RowSquare [6,4,2,2,2,2,1,1] [6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg4067

lemma sg7475 : RowSquare [6,4,2,2,2,2,1,1] [6,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg4068

lemma sg7476 : RowSquare [6,4,2,2,2,2,1,1] [6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15 sg4069

lemma sg7477 : RowSquare [6,4,2,2,2,2,1,1] [6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg4080

lemma sg7478 : RowSquare [6,4,2,2,2,2,1,1] [6,6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg4081

lemma sg7479 : RowSquare [6,4,2,2,2,2,1,1] [7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg4072

lemma sg7480 : RowSquare [6,4,3,2,1,1,1,1,1] [3,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg2626

lemma sg7481 : RowSquare [6,4,3,2,1,1,1,1,1] [3,3,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg2626

lemma sg7482 : RowSquare [6,4,3,2,1,1,1,1,1] [3,3,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg2626

lemma sg7483 : RowSquare [6,4,3,2,1,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg4862

lemma sg7484 : RowSquare [6,4,3,2,1,1,1,1,1] [4,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg2626

lemma sg7485 : RowSquare [6,4,3,2,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg2627

lemma sg7486 : RowSquare [6,4,3,2,1,1,1,1,1] [4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg6155

lemma sg7487 : RowSquare [6,4,3,2,1,1,1,1,1] [4,4,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg2626

lemma sg7488 : RowSquare [6,4,3,2,1,1,1,1,1] [5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg4864

lemma sg7489 : RowSquare [6,4,3,2,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg2626

lemma sg7490 : RowSquare [6,4,3,2,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg2627

lemma sg7491 : RowSquare [6,4,3,2,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg2626

lemma sg7492 : RowSquare [6,4,3,2,1,1,1,1,1] [5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg6162

lemma sg7493 : RowSquare [6,4,3,2,1,1,1,1,1] [5,4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg2627

lemma sg7494 : RowSquare [6,4,3,2,1,1,1,1,1] [5,4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6163

lemma sg7495 : RowSquare [6,4,3,2,1,1,1,1,1] [5,5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg514 sg1329

lemma sg7496 : RowSquare [6,4,3,2,1,1,1,1,1] [5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4637

lemma sg7497 : RowSquare [6,4,3,2,1,1,1,1,1] [5,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4638

lemma sg7498 : RowSquare [6,4,3,2,1,1,1,1,1] [5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg2491

lemma sg7499 : RowSquare [6,4,3,2,1,1,1,1,1] [5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg2492

lemma sg7500 : RowSquare [6,4,3,2,1,1,1,1,1] [5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg32 sg3179

lemma sg7501 : RowSquare [6,4,3,2,1,1,1,1,1] [5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg32 sg3180

lemma sg7502 : RowSquare [6,4,3,2,1,1,1,1,1] [5,5,5,5] := by
  exact rowSquare_join (by decide) sg390 sg1631

lemma sg7503 : RowSquare [6,4,3,2,1,1,1,1,1] [6,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5366

lemma sg7504 : RowSquare [6,4,3,2,1,1,1,1,1] [6,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4641

lemma sg7505 : RowSquare [6,4,3,2,1,1,1,1,1] [6,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg2520

lemma sg7506 : RowSquare [6,4,3,2,1,1,1,1,1] [6,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg2493

lemma sg7507 : RowSquare [6,4,3,2,1,1,1,1,1] [6,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg2494

lemma sg7508 : RowSquare [6,4,3,2,1,1,1,1,1] [6,6,5,2,1] := by
  exact rowSquare_join (by decide) sg76 sg2491

lemma sg7509 : RowSquare [6,4,3,2,1,1,1,1,1] [6,6,5,3] := by
  exact rowSquare_join (by decide) sg76 sg2492

lemma sg7510 : RowSquare [6,4,3,2,1,1,1,1,1] [6,6,6,1,1] := by
  exact rowSquare_join (by decide) sg77 sg2491

lemma sg7511 : RowSquare [6,4,3,2,1,1,1,1,1] [6,6,6,2] := by
  exact rowSquare_join (by decide) sg77 sg2492

lemma sg7512 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1327

lemma sg7513 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1327

lemma sg7514 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg1329

lemma sg7515 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1327

lemma sg7516 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1327

lemma sg7517 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1331

lemma sg7518 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1332

lemma sg7519 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg591 sg1327

lemma sg7520 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg592 sg1327

lemma sg7521 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg593 sg1327

lemma sg7522 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg1330

lemma sg7523 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg1327

lemma sg7524 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg1331

lemma sg7525 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg1332

lemma sg7526 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg595 sg1327

lemma sg7527 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1338

lemma sg7528 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg998 sg889

lemma sg7529 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg1327

lemma sg7530 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1339

lemma sg7531 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1340

lemma sg7532 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg1331

lemma sg7533 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg588 sg1332

lemma sg7534 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg1330

lemma sg7535 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1330

lemma sg7536 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg589 sg1332

lemma sg7537 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg590 sg1331

lemma sg7538 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg1001 sg892

lemma sg7539 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg597 sg1327

lemma sg7540 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6180

lemma sg7541 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg598 sg1327

lemma sg7542 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6181

lemma sg7543 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6182

lemma sg7544 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg599 sg1327

lemma sg7545 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6183

lemma sg7546 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6184

lemma sg7547 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6185

lemma sg7548 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6186

lemma sg7549 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg591 sg1331

lemma sg7550 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6187

lemma sg7551 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg591 sg1332

lemma sg7552 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg600 sg1327

lemma sg7553 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6188

lemma sg7554 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6189

lemma sg7555 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg601 sg1327

lemma sg7556 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6190

lemma sg7557 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6191

lemma sg7558 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6192

lemma sg7559 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6193

lemma sg7560 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6194

lemma sg7561 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6195

lemma sg7562 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6196

lemma sg7563 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg592 sg1332

lemma sg7564 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg593 sg1330

lemma sg7565 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6197

lemma sg7566 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg1330

lemma sg7567 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6198

lemma sg7568 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6199

lemma sg7569 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg6200

lemma sg7570 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg594 sg1331

lemma sg7571 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6201

lemma sg7572 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg0 sg6202

lemma sg7573 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg602 sg1327

lemma sg7574 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1348

lemma sg7575 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg998 sg897

lemma sg7576 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg1338

lemma sg7577 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1349

lemma sg7578 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg898

lemma sg7579 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg999 sg897

lemma sg7580 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg899

lemma sg7581 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1340

lemma sg7582 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1000 sg897

lemma sg7583 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1006 sg892

lemma sg7584 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg596 sg1330

lemma sg7585 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg999 sg898

lemma sg7586 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg1339

lemma sg7587 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg899

lemma sg7588 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1000 sg898

lemma sg7589 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg1001 sg898

lemma sg7590 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg899

lemma sg7591 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg1001 sg899

lemma sg7592 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg603 sg1327

lemma sg7593 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5367

lemma sg7594 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6203

lemma sg7595 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg604 sg1327

lemma sg7596 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5368

lemma sg7597 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5369

lemma sg7598 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg605 sg1327

lemma sg7599 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5370

lemma sg7600 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6204

lemma sg7601 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4643

lemma sg7602 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5371

lemma sg7603 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6206

lemma sg7604 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5372

lemma sg7605 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5373

lemma sg7606 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg597 sg1332

lemma sg7607 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6209

lemma sg7608 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5374

lemma sg7609 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6210

lemma sg7610 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6211

lemma sg7611 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5375

lemma sg7612 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4644

lemma sg7613 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5376

lemma sg7614 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6213

lemma sg7615 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5377

lemma sg7616 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg5378

lemma sg7617 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg599 sg1330

lemma sg7618 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4645

lemma sg7619 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg6215

lemma sg7620 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4646

lemma sg7621 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5379

lemma sg7622 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,4,3,3] := by
  exact rowSquare_join (by decide) sg1 sg5380

lemma sg7623 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5381

lemma sg7624 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,4,4,4,2] := by
  exact rowSquare_join (by decide) sg1 sg5382

lemma sg7625 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg607 sg1327

lemma sg7626 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6221

lemma sg7627 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6222

lemma sg7628 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6223

lemma sg7629 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6224

lemma sg7630 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6225

lemma sg7631 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6226

lemma sg7632 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4647

lemma sg7633 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6228

lemma sg7634 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6229

lemma sg7635 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg6230

lemma sg7636 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg601 sg1330

lemma sg7637 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6231

lemma sg7638 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4648

lemma sg7639 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4649

lemma sg7640 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,4,3,2] := by
  exact rowSquare_join (by decide) sg0 sg6232

lemma sg7641 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg6233

lemma sg7642 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,5,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4650

lemma sg7643 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,5,3,1] := by
  exact rowSquare_join (by decide) sg4 sg4651

lemma sg7644 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,5,5,4] := by
  exact rowSquare_join (by decide) sg4 sg4652

lemma sg7645 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg1358

lemma sg7646 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg902

lemma sg7647 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg1348

lemma sg7648 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1006 sg897

lemma sg7649 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg903

lemma sg7650 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg902

lemma sg7651 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg1006 sg898

lemma sg7652 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg902

lemma sg7653 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,3,3,2] := by
  exact rowSquare_join (by decide) sg1001 sg902

lemma sg7654 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg903

lemma sg7655 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg903

lemma sg7656 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,4,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg903

lemma sg7657 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,4,3,1] := by
  exact rowSquare_join (by decide) sg1007 sg899

lemma sg7658 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [6,6,4,4] := by
  exact rowSquare_join (by decide) sg1008 sg899

lemma sg7659 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg608 sg1327

lemma sg7660 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg603 sg1328

lemma sg7661 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5383

lemma sg7662 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg5384

lemma sg7663 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg609 sg1327

lemma sg7664 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg604 sg1328

lemma sg7665 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5385

lemma sg7666 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5386

lemma sg7667 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg4643

lemma sg7668 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg605 sg1328

lemma sg7669 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5387

lemma sg7670 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5388

lemma sg7671 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4653

lemma sg7672 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5389

lemma sg7673 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3803

lemma sg7674 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg1 sg5390

lemma sg7675 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg5391

lemma sg7676 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg610 sg1327

lemma sg7677 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg606 sg1328

lemma sg7678 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5392

lemma sg7679 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5393

lemma sg7680 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg4644

lemma sg7681 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5394

lemma sg7682 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5395

lemma sg7683 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4654

lemma sg7684 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4655

lemma sg7685 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3804

lemma sg7686 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg3805

lemma sg7687 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg5396

lemma sg7688 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg605 sg1330

lemma sg7689 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg3806

lemma sg7690 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4656

lemma sg7691 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4657

lemma sg7692 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,4,3,2] := by
  exact rowSquare_join (by decide) sg13 sg3807

lemma sg7693 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,4,4,4,1] := by
  exact rowSquare_join (by decide) sg13 sg3808

lemma sg7694 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg607 sg1328

lemma sg7695 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6261

lemma sg7696 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5397

lemma sg7697 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6263

lemma sg7698 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5 sg4647

lemma sg7699 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,5,4,4] := by
  exact rowSquare_join (by decide) sg13 sg3810

lemma sg7700 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,5,5,2,1] := by
  exact rowSquare_join (by decide) sg13 sg3811

lemma sg7701 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,5,5,3] := by
  exact rowSquare_join (by decide) sg13 sg3812

lemma sg7702 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6275

lemma sg7703 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6276

lemma sg7704 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,6,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg6277

lemma sg7705 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg6278

lemma sg7706 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4658

lemma sg7707 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,6,4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg4659

lemma sg7708 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,6,4,3] := by
  exact rowSquare_join (by decide) sg4 sg4660

lemma sg7709 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,6,5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4661

lemma sg7710 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,6,5,2] := by
  exact rowSquare_join (by decide) sg4 sg4662

lemma sg7711 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg998 sg909

lemma sg7712 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg999 sg909

lemma sg7713 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1000 sg909

lemma sg7714 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,2,2,2] := by
  exact rowSquare_join (by decide) sg1001 sg909

lemma sg7715 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1006 sg903

lemma sg7716 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,3,2,1] := by
  exact rowSquare_join (by decide) sg1007 sg902

lemma sg7717 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,3,3] := by
  exact rowSquare_join (by decide) sg1008 sg902

lemma sg7718 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,4,1,1] := by
  exact rowSquare_join (by decide) sg1007 sg903

lemma sg7719 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [7,7,4,2] := by
  exact rowSquare_join (by decide) sg1008 sg903

lemma sg7720 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg611 sg1327

lemma sg7721 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg608 sg1328

lemma sg7722 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5399

lemma sg7723 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5400

lemma sg7724 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg6 sg4643

lemma sg7725 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg612 sg1327

lemma sg7726 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg609 sg1328

lemma sg7727 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5401

lemma sg7728 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5402

lemma sg7729 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg4653

lemma sg7730 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5403

lemma sg7731 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg5404

lemma sg7732 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg4663

lemma sg7733 : RowSquare [6,5,1,1,1,1,1,1,1,1,1] [8,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg4664

end UniversalTensorSquare
end
end

end OAI
