import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes31
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes36

namespace OAI

/-! Semigroup Nodes 37. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg15340 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3434

lemma sg15341 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,2,2,2] := by
  exact rowSquare_join (by decide) sg3701 sg3368

lemma sg15342 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg3427

lemma sg15343 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg3360 sg3706

lemma sg15344 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,5,4,2] := by
  exact rowSquare_join (by decide) sg3725 sg3339

lemma sg15345 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4526

lemma sg15346 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3000 sg4238

lemma sg15347 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,2] := by
  exact rowSquare_join (by decide) sg3725 sg3340

lemma sg15348 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg3725 sg3341

lemma sg15349 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,5] := by
  exact rowSquare_join (by decide) sg3726 sg3341

lemma sg15350 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg4340

lemma sg15351 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2760 sg4407

lemma sg15352 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2760 sg4408

lemma sg15353 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3428

lemma sg15354 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2760 sg4409

lemma sg15355 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2762 sg4408

lemma sg15356 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3429

lemma sg15357 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3430

lemma sg15358 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg3360 sg3707

lemma sg15359 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3002 sg4236

lemma sg15360 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3431

lemma sg15361 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg3004 sg4236

lemma sg15362 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg3419 sg3642

lemma sg15363 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2762 sg4409

lemma sg15364 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3432

lemma sg15365 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg3429

lemma sg15366 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3433

lemma sg15367 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg3360 sg3708

lemma sg15368 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg3360 sg3709

lemma sg15369 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3434

lemma sg15370 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,2] := by
  exact rowSquare_join (by decide) sg3360 sg3710

lemma sg15371 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,1] := by
  exact rowSquare_join (by decide) sg3419 sg3643

lemma sg15372 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,5] := by
  exact rowSquare_join (by decide) sg3420 sg3643

lemma sg15373 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3002 sg4238

lemma sg15374 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,2,2] := by
  exact rowSquare_join (by decide) sg3004 sg4238

lemma sg15375 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,3,1] := by
  exact rowSquare_join (by decide) sg3725 sg3342

lemma sg15376 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,7,6,6,4] := by
  exact rowSquare_join (by decide) sg3726 sg3342

lemma sg15377 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1897 sg5753

lemma sg15378 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3633 sg3435

lemma sg15379 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg3638 sg3421

lemma sg15380 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2930 sg4330

lemma sg15381 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3436

lemma sg15382 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3633 sg3437

lemma sg15383 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3635 sg3435

lemma sg15384 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3363 sg3704

lemma sg15385 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2931 sg4330

lemma sg15386 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3438

lemma sg15387 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3638 sg3424

lemma sg15388 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2930 sg4333

lemma sg15389 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3701 sg3369

lemma sg15390 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3636 sg3435

lemma sg15391 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3363 sg3705

lemma sg15392 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3439

lemma sg15393 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2933 sg4330

lemma sg15394 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg3360 sg3713

lemma sg15395 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3363 sg3706

lemma sg15396 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2934 sg4330

lemma sg15397 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3441

lemma sg15398 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg3713 sg3361

lemma sg15399 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg3713 sg3362

lemma sg15400 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3633 sg3442

lemma sg15401 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3635 sg3437

lemma sg15402 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2616 sg4521

lemma sg15403 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3701 sg3370

lemma sg15404 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3639 sg3422

lemma sg15405 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3363 sg3707

lemma sg15406 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3443

lemma sg15407 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2937 sg4330

lemma sg15408 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3444

lemma sg15409 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg3704 sg3364

lemma sg15410 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3636 sg3437

lemma sg15411 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2616 sg4522

lemma sg15412 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3445

lemma sg15413 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3363 sg3708

lemma sg15414 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3363 sg3709

lemma sg15415 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3446

lemma sg15416 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3440

lemma sg15417 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg3360 sg3714

lemma sg15418 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3363 sg3710

lemma sg15419 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3447

lemma sg15420 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3441

lemma sg15421 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg3728 sg3340

lemma sg15422 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg3728 sg3341

lemma sg15423 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3640 sg3424

lemma sg15424 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2932 sg4333

lemma sg15425 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2616 sg4524

lemma sg15426 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3448

lemma sg15427 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3363 sg3711

lemma sg15428 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3449

lemma sg15429 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,2,2] := by
  exact rowSquare_join (by decide) sg3701 sg3371

lemma sg15430 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3727 sg3343

lemma sg15431 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg3360 sg3715

lemma sg15432 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3363 sg3712

lemma sg15433 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3727 sg3344

lemma sg15434 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg3360 sg3716

lemma sg15435 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3010 sg4238

lemma sg15436 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg3729 sg3340

lemma sg15437 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg3725 sg3345

lemma sg15438 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,4] := by
  exact rowSquare_join (by decide) sg3726 sg3345

lemma sg15439 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3635 sg3442

lemma sg15440 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2617 sg4521

lemma sg15441 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3701 sg3372

lemma sg15442 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3636 sg3442

lemma sg15443 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2617 sg4522

lemma sg15444 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3451

lemma sg15445 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4527

lemma sg15446 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2937 sg4332

lemma sg15447 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3452

lemma sg15448 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3444

lemma sg15449 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg3704 sg3366

lemma sg15450 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3424 sg3641

lemma sg15451 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4528

lemma sg15452 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2617 sg4524

lemma sg15453 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3453

lemma sg15454 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4529

lemma sg15455 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3454

lemma sg15456 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3446

lemma sg15457 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg3360 sg3717

lemma sg15458 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4530

lemma sg15459 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3447

lemma sg15460 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg3728 sg3342

lemma sg15461 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2938 sg4333

lemma sg15462 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4531

lemma sg15463 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3633 sg3455

lemma sg15464 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3448

lemma sg15465 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg3360 sg3718

lemma sg15466 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2614 sg4532

lemma sg15467 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3449

lemma sg15468 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg3447

lemma sg15469 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg3360 sg3719

lemma sg15470 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,1] := by
  exact rowSquare_join (by decide) sg3725 sg3346

lemma sg15471 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,7,6,6,3] := by
  exact rowSquare_join (by decide) sg3726 sg3346

lemma sg15472 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2760 sg4411

lemma sg15473 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2765 sg4408

lemma sg15474 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2762 sg4411

lemma sg15475 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3451

lemma sg15476 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3002 sg4245

lemma sg15477 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3635 sg3452

lemma sg15478 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [8,8,5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3636 sg3451

lemma sg15479 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3701 sg3373

lemma sg15480 : RowSquare [4,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [9,6,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3701 sg3374

lemma sg15481 : RowSquare [5,5,3,3,2,2,2,2,2,2,1,1] [5,5,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2361 sg4832

lemma sg15482 : RowSquare [5,5,3,3,2,2,2,2,2,2,1,1] [5,5,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2362 sg4832

lemma sg15483 : RowSquare [5,5,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2363 sg4832

lemma sg15484 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1736 sg5776

lemma sg15485 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2282 sg4917

lemma sg15486 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1737 sg5776

lemma sg15487 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg3413

lemma sg15488 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,4,4,1] := by
  exact rowSquare_join (by decide) sg2647 sg4488

lemma sg15489 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3686 sg3359

lemma sg15490 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg5787

lemma sg15491 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg2281 sg4924

lemma sg15492 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg5788

lemma sg15493 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg4324

lemma sg15494 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1686 sg5789

lemma sg15495 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg1688 sg5789

lemma sg15496 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3691 sg3359

lemma sg15497 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg2651 sg4488

lemma sg15498 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2139 sg5001

lemma sg15499 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3409 sg3626

lemma sg15500 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3695 sg3359

lemma sg15501 : RowSquare [5,5,3,3,3,2,1,1,1,1,1,1,1,1,1] [7,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2838 sg4360

lemma sg15502 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg849 sg8018

lemma sg15503 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg3562 sg3475

lemma sg15504 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg5781

lemma sg15505 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg3562 sg3476

lemma sg15506 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg1688 sg5782

lemma sg15507 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg1688 sg5783

lemma sg15508 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,4,3] := by
  exact rowSquare_join (by decide) sg3356 sg3690

lemma sg15509 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2798 sg4361

lemma sg15510 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg1688 sg5785

lemma sg15511 : RowSquare [5,5,4,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg1033 sg8001

lemma sg15512 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [4,4,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1478 sg6457

lemma sg15513 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1852 sg5672

lemma sg15514 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,4,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1479 sg6457

lemma sg15515 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1480 sg6457

lemma sg15516 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg5672

lemma sg15517 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1481 sg6457

lemma sg15518 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1855 sg5672

lemma sg15519 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,5,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1856 sg5672

lemma sg15520 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1482 sg6457

lemma sg15521 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [5,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1857 sg5672

lemma sg15522 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1858 sg5672

lemma sg15523 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1483 sg6457

lemma sg15524 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1859 sg5672

lemma sg15525 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1852 sg5673

lemma sg15526 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1860 sg5672

lemma sg15527 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,4,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1484 sg6457

lemma sg15528 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,4,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1861 sg5672

lemma sg15529 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1485 sg6457

lemma sg15530 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,4,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1853 sg5673

lemma sg15531 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1486 sg6457

lemma sg15532 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1862 sg5672

lemma sg15533 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1854 sg5673

lemma sg15534 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1487 sg6457

lemma sg15535 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,5,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1855 sg5673

lemma sg15536 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1488 sg6457

lemma sg15537 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [6,6,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1863 sg5672

lemma sg15538 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1864 sg5672

lemma sg15539 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1489 sg6457

lemma sg15540 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1865 sg5672

lemma sg15541 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,3,3,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1858 sg5673

lemma sg15542 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,3,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1859 sg5673

lemma sg15543 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1490 sg6457

lemma sg15544 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1866 sg5672

lemma sg15545 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,4,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1860 sg5673

lemma sg15546 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1491 sg6457

lemma sg15547 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1492 sg6457

lemma sg15548 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,5,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1862 sg5673

lemma sg15549 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1493 sg6457

lemma sg15550 : RowSquare [6,5,3,2,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1867 sg5672

lemma sg15551 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,5,4] := by
  exact rowSquare_join (by decide) sg2167 sg4949

lemma sg15552 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg2746 sg4378

lemma sg15553 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg2746 sg4379

lemma sg15554 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg2633 sg4496

lemma sg15555 : RowSquare [6,5,3,3,2,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3691 sg3353

lemma sg15556 : RowSquare [6,5,3,3,2,2,2,2,2,2,1] [5,5,3,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1747 sg5674

lemma sg15557 : RowSquare [6,5,3,3,2,2,2,2,2,2,1] [6,6,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1326 sg6457

lemma sg15558 : RowSquare [6,5,3,3,2,2,2,2,2,2,1] [6,6,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1325 sg6458

lemma sg15559 : RowSquare [6,5,3,3,3,2,1,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3691 sg3298

lemma sg15560 : RowSquare [6,5,4,3,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg2633 sg4455

lemma sg15561 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [4,4,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1075 sg7812

lemma sg15562 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [5,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1076 sg7812

lemma sg15563 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [5,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg7812

lemma sg15564 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [5,5,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1078 sg7812

lemma sg15565 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [5,5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1075 sg7815

lemma sg15566 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1079 sg7812

lemma sg15567 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1076 sg7813

lemma sg15568 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1080 sg7812

lemma sg15569 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1081 sg7812

lemma sg15570 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg7813

lemma sg15571 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1082 sg7812

lemma sg15572 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,5,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg7815

lemma sg15573 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,5,5,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg7816

lemma sg15574 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1078 sg7815

lemma sg15575 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [6,6,6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1075 sg7836

lemma sg15576 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1083 sg7812

lemma sg15577 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1084 sg7812

lemma sg15578 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,3,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1079 sg7813

lemma sg15579 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1085 sg7812

lemma sg15580 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1080 sg7813

lemma sg15581 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,4,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1081 sg7813

lemma sg15582 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg7822

lemma sg15583 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1086 sg7812

lemma sg15584 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1082 sg7813

lemma sg15585 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [7,5,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg7823

lemma sg15586 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [8,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1087 sg7812

lemma sg15587 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [8,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1088 sg7812

lemma sg15588 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [8,3,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1083 sg7813

lemma sg15589 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [8,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1084 sg7813

lemma sg15590 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [8,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1089 sg7812

lemma sg15591 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [8,4,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1085 sg7813

lemma sg15592 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [8,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1077 sg7841

lemma sg15593 : RowSquare [6,6,2,2,2,2,2,2,2,2,1,1] [8,5,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1086 sg7813

lemma sg15594 : RowSquare [6,6,3,2,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1754 sg5768

lemma sg15595 : RowSquare [6,6,3,2,2,2,2,2,2,2,1] [5,5,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg662 sg8780

lemma sg15596 : RowSquare [6,6,3,2,2,2,2,2,2,2,1] [6,6,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg993 sg7812

lemma sg15597 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1] [5,4,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3325 sg3403

lemma sg15598 : RowSquare [6,6,3,3,3,2,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3556 sg3298

lemma sg15599 : RowSquare [7,5,3,3,2,1,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4918

lemma sg15600 : RowSquare [7,5,3,3,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2256 sg4917

lemma sg15601 : RowSquare [7,6,2,2,2,2,2,2,2,2,1] [6,6,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg367 sg10872

lemma sg15602 : RowSquare [7,6,2,2,2,2,2,2,2,2,1] [6,6,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg367 sg10874

lemma sg15603 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg2708 sg4376

lemma sg15604 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4378

lemma sg15605 : RowSquare [7,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4388

lemma sg15606 : RowSquare [7,6,3,2,2,2,2,2,2,1,1] [7,7,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg363 sg10881

lemma sg15607 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4165

lemma sg15608 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2626 sg4167

lemma sg15609 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2627 sg4167

lemma sg15610 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2628 sg4165

lemma sg15611 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2628 sg4167

lemma sg15612 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [5,5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg2632 sg4173

lemma sg15613 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [6,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg4 sg14313

lemma sg15614 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [6,6,6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg390 sg11051

lemma sg15615 : RowSquare [7,6,3,3,2,2,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3404 sg3316

lemma sg15616 : RowSquare [7,6,4,3,2,1,1,1,1,1,1,1,1] [3,3,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1327 sg6469

lemma sg15617 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4366

lemma sg15618 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,3,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4369

lemma sg15619 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2708 sg4368

lemma sg15620 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg2708 sg4369

lemma sg15621 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg2709 sg4368

lemma sg15622 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg2710 sg4369

lemma sg15623 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2710 sg4371

lemma sg15624 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg2881 sg4295

lemma sg15625 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2710 sg4372

lemma sg15626 : RowSquare [7,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4373

lemma sg15627 : RowSquare [7,7,2,2,2,2,2,2,2,1,1] [5,5,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg97 sg11811

lemma sg15628 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg4167

lemma sg15629 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2880 sg4167

lemma sg15630 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2879 sg4169

lemma sg15631 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2885 sg4167

lemma sg15632 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,5,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg2883 sg4168

lemma sg15633 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,5,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg2882 sg4169

lemma sg15634 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [7,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2884 sg4169

lemma sg15635 : RowSquare [7,7,3,2,1,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg2886 sg4169

lemma sg15636 : RowSquare [7,7,3,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2156 sg4878

lemma sg15637 : RowSquare [7,7,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4861

lemma sg15638 : RowSquare [7,7,3,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg12917

lemma sg15639 : RowSquare [7,7,3,3,2,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg12918

lemma sg15640 : RowSquare [8,6,3,2,2,2,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3404 sg3309

lemma sg15641 : RowSquare [8,6,3,3,2,1,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3556 sg3265

lemma sg15642 : RowSquare [8,7,2,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2706 sg4348

lemma sg15643 : RowSquare [8,7,2,2,1,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4348

lemma sg15644 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4024

lemma sg15645 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4026

lemma sg15646 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1] [5,5,3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2702 sg4030

lemma sg15647 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1] [5,5,4,4,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12920

lemma sg15648 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1] [5,5,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg12333

lemma sg15649 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12335

lemma sg15650 : RowSquare [8,7,3,2,2,1,1,1,1,1,1,1,1] [6,6,6,4,4,4] := by
  exact rowSquare_join (by decide) sg74 sg12336

lemma sg15651 : RowSquare [8,7,3,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg14531

lemma sg15652 : RowSquare [8,7,3,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg14532

lemma sg15653 : RowSquare [8,7,3,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg12954

lemma sg15654 : RowSquare [8,7,3,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg12 sg12955

lemma sg15655 : RowSquare [8,7,3,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg12 sg12956

lemma sg15656 : RowSquare [8,8,2,2,2,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2576 sg4348

lemma sg15657 : RowSquare [8,8,2,2,2,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3275

lemma sg15658 : RowSquare [8,8,2,2,2,1,1,1,1,1,1,1,1] [5,4,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2578 sg4348

lemma sg15659 : RowSquare [8,8,2,2,2,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3275 sg3532

lemma sg15660 : RowSquare [8,8,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3259

lemma sg15661 : RowSquare [8,8,3,2,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3260

lemma sg15662 : RowSquare [8,8,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg3260

lemma sg15663 : RowSquare [8,8,3,2,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3262

lemma sg15664 : RowSquare [8,8,3,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3263

lemma sg15665 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2251 sg4834

lemma sg15666 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4837

lemma sg15667 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2254 sg4834

lemma sg15668 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg11733

lemma sg15669 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4839

lemma sg15670 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4841

lemma sg15671 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2256 sg4834

lemma sg15672 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2251 sg4842

lemma sg15673 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg11734

lemma sg15674 : RowSquare [9,7,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,6] := by
  exact rowSquare_join (by decide) sg32 sg12707

lemma sg15675 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [3,3,3,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12921

lemma sg15676 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12924

lemma sg15677 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12925

lemma sg15678 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12926

lemma sg15679 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [4,4,4,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12927

lemma sg15680 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3522 sg3256

lemma sg15681 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg11733

lemma sg15682 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3524 sg3258

lemma sg15683 : RowSquare [9,8,2,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3525 sg3258

lemma sg15684 : RowSquare [9,8,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3231

lemma sg15685 : RowSquare [9,8,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3230

lemma sg15686 : RowSquare [9,8,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3229

lemma sg15687 : RowSquare [9,8,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3228

lemma sg15688 : RowSquare [9,8,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3292 sg3226

lemma sg15689 : RowSquare [9,8,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2566 sg3982

lemma sg15690 : RowSquare [9,8,2,2,2,2,2,2,1] [4,4,4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3288 sg3227

lemma sg15691 : RowSquare [9,8,2,2,2,2,2,2,1] [4,4,4,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3290 sg3225

lemma sg15692 : RowSquare [9,8,2,2,2,2,2,2,1] [5,5,5,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg3286 sg3222

lemma sg15693 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1,1] [4,4,4,4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg11755

lemma sg15694 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14526

lemma sg15695 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12935

lemma sg15696 : RowSquare [10,8,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg12936

lemma sg15697 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2925 sg4882

lemma sg15698 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3362 sg4439

lemma sg15699 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [5,5,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg4883

lemma sg15700 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,5,5,5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2614 sg4992

lemma sg15701 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg3417 sg4397

lemma sg15702 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg3420 sg4396

lemma sg15703 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,5,5,5,2,2] := by
  exact rowSquare_join (by decide) sg3420 sg4397

lemma sg15704 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3563 sg4327

lemma sg15705 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3632 sg4222

lemma sg15706 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3688 sg4124

lemma sg15707 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,3,3,3] := by
  exact rowSquare_join (by decide) sg2925 sg4884

lemma sg15708 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3613 sg4237

lemma sg15709 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg3632 sg4224

lemma sg15710 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg3420 sg4398

lemma sg15711 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3302 sg4526

lemma sg15712 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3632 sg4226

lemma sg15713 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [6,6,6,6,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2902 sg4887

lemma sg15714 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2717 sg4926

lemma sg15715 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3363 sg4440

lemma sg15716 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3559 sg4330

lemma sg15717 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,4,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg0 sg15295

lemma sg15718 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg2718 sg4926

lemma sg15719 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3559 sg4332

lemma sg15720 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3559 sg4333

lemma sg15721 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3363 sg4442

lemma sg15722 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3559 sg4334

lemma sg15723 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg3421 sg4398

lemma sg15724 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4239

lemma sg15725 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3692 sg4124

lemma sg15726 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3421 sg4399

lemma sg15727 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4240

lemma sg15728 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg0 sg15296

lemma sg15729 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4241

lemma sg15730 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4125

lemma sg15731 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3561 sg4332

lemma sg15732 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3422 sg4399

lemma sg15733 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3685 sg4127

lemma sg15734 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,4,4] := by
  exact rowSquare_join (by decide) sg3704 sg4119

lemma sg15735 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,5,5,5,3] := by
  exact rowSquare_join (by decide) sg3704 sg4120

lemma sg15736 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3563 sg4333

lemma sg15737 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3563 sg4334

lemma sg15738 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3424 sg4398

lemma sg15739 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,6,6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3614 sg4242

end UniversalTensorSquare
end
end

end OAI
