import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes51

namespace OAI

/-! Semigroup Nodes 52. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg21340 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg15685

lemma sg21341 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg15686

lemma sg21342 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg15687

lemma sg21343 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg44 sg15688

lemma sg21344 : RowSquare [9,8,2,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg44 sg15689

lemma sg21345 : RowSquare [10,8,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3264 sg8009

lemma sg21346 : RowSquare [10,8,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg15294

lemma sg21347 : RowSquare [10,8,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,5,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3268 sg8009

lemma sg21348 : RowSquare [10,8,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,5,4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3264 sg8010

lemma sg21349 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,7,7,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5440

lemma sg21350 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,7,7,7,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4829 sg5348

lemma sg21351 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5447

lemma sg21352 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,7,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4789 sg5428

lemma sg21353 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4826 sg5350

lemma sg21354 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,7,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5445

lemma sg21355 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,7,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5448

lemma sg21356 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,7,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5446

lemma sg21357 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5449

lemma sg21358 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,7,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5450

lemma sg21359 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,7,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5447

lemma sg21360 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,8,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg3984 sg6123

lemma sg21361 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,8,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5448

lemma sg21362 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,8,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4831 sg5347

lemma sg21363 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,8,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5449

lemma sg21364 : RowSquare [10,8,4,3,2,2,2,2,1,1] [8,8,8,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4929 sg5011

lemma sg21365 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5467

lemma sg21366 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,7,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4854 sg5261

lemma sg21367 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,7,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4827 sg5350

lemma sg21368 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,7,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5626

lemma sg21369 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,7,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5471

lemma sg21370 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,7,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5472

lemma sg21371 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,7,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4851 sg5269

lemma sg21372 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,7,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4851 sg5270

lemma sg21373 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,7,7,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4929 sg5012

lemma sg21374 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4854 sg5264

lemma sg21375 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4826 sg5353

lemma sg21376 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5627

lemma sg21377 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5479

lemma sg21378 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5480

lemma sg21379 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5469

lemma sg21380 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,6,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5470

lemma sg21381 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4853 sg5267

lemma sg21382 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5628

lemma sg21383 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,7,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5481

lemma sg21384 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,7,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5471

lemma sg21385 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,7,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5472

lemma sg21386 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,7,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4929 sg5013

lemma sg21387 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,8,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5482

lemma sg21388 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,8,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5471

lemma sg21389 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,8,8,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4929 sg5014

lemma sg21390 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4788 sg5441

lemma sg21391 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4825 sg5354

lemma sg21392 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5473

lemma sg21393 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4830 sg5349

lemma sg21394 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5629

lemma sg21395 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4788 sg5442

lemma sg21396 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5473

lemma sg21397 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4825 sg5355

lemma sg21398 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5630

lemma sg21399 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4788 sg5443

lemma sg21400 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5631

lemma sg21401 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5474

lemma sg21402 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5475

lemma sg21403 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,5,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4788 sg5444

lemma sg21404 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,5,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5632

lemma sg21405 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,5,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5476

lemma sg21406 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,5,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5474

lemma sg21407 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,5,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5477

lemma sg21408 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,5,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5478

lemma sg21409 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,6,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5633

lemma sg21410 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,6,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5476

lemma sg21411 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,6,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5479

lemma sg21412 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,6,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5480

lemma sg21413 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,6,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5478

lemma sg21414 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4788 sg5448

lemma sg21415 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,7,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5481

lemma sg21416 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,7,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4929 sg5015

lemma sg21417 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,8,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5482

lemma sg21418 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,8,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4929 sg5016

lemma sg21419 : RowSquare [10,8,4,3,2,2,2,2,1,1] [9,9,9,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4929 sg5017

lemma sg21420 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg25 sg15651

lemma sg21421 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg25 sg15652

lemma sg21422 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg15653

lemma sg21423 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg24 sg15654

lemma sg21424 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg24 sg15655

lemma sg21425 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg11731

lemma sg21426 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg72 sg15245

lemma sg21427 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg72 sg15246

lemma sg21428 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4755 sg5524

lemma sg21429 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5451

lemma sg21430 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4719 sg5621

lemma sg21431 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3935 sg6357

lemma sg21432 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4756 sg5524

lemma sg21433 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5452

lemma sg21434 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5431

lemma sg21435 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4720 sg5617

lemma sg21436 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4757 sg5524

lemma sg21437 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5453

lemma sg21438 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5432

lemma sg21439 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4793 sg5424

lemma sg21440 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4722 sg5615

lemma sg21441 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5454

lemma sg21442 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5433

lemma sg21443 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4793 sg5425

lemma sg21444 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4795 sg5414

lemma sg21445 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4857 sg5240

lemma sg21446 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4795 sg5415

lemma sg21447 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3988 sg6118

lemma sg21448 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,3,3,3,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg4739 sg5525

lemma sg21449 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1288 sg11732

lemma sg21450 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg73 sg15245

lemma sg21451 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg73 sg15246

lemma sg21452 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4758 sg5524

lemma sg21453 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5455

lemma sg21454 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4719 sg5622

lemma sg21455 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3935 sg6358

lemma sg21456 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4759 sg5524

lemma sg21457 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5456

lemma sg21458 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5434

lemma sg21459 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4720 sg5618

lemma sg21460 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4760 sg5524

lemma sg21461 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5457

lemma sg21462 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4738 sg5578

lemma sg21463 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4791 sg5431

lemma sg21464 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4721 sg5617

lemma sg21465 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4761 sg5524

lemma sg21466 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5458

lemma sg21467 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4738 sg5579

lemma sg21468 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4791 sg5432

lemma sg21469 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4794 sg5424

lemma sg21470 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4738 sg5580

lemma sg21471 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4855 sg5258

lemma sg21472 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4794 sg5425

lemma sg21473 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg4718 sg5634

lemma sg21474 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4858 sg5240

lemma sg21475 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg4796 sg5415

lemma sg21476 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4762 sg5524

lemma sg21477 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5459

lemma sg21478 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5435

lemma sg21479 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4720 sg5619

lemma sg21480 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4763 sg5524

lemma sg21481 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5460

lemma sg21482 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4735 sg5588

lemma sg21483 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4793 sg5426

lemma sg21484 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4722 sg5616

lemma sg21485 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4764 sg5524

lemma sg21486 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5461

lemma sg21487 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4735 sg5589

lemma sg21488 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4734 sg5595

lemma sg21489 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4873 sg5128

lemma sg21490 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5462

lemma sg21491 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4735 sg5590

lemma sg21492 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4849 sg5271

lemma sg21493 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4792 sg5432

lemma sg21494 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4784 sg5483

lemma sg21495 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4849 sg5272

lemma sg21496 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4873 sg5129

lemma sg21497 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4718 sg5635

lemma sg21498 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4859 sg5240

lemma sg21499 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4765 sg5524

lemma sg21500 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5463

lemma sg21501 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5436

lemma sg21502 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4736 sg5588

lemma sg21503 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4795 sg5421

lemma sg21504 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4766 sg5524

lemma sg21505 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5464

lemma sg21506 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5437

lemma sg21507 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4734 sg5596

lemma sg21508 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4737 sg5588

lemma sg21509 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4822 sg5357

lemma sg21510 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5438

lemma sg21511 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4736 sg5590

lemma sg21512 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4850 sg5271

lemma sg21513 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4784 sg5484

lemma sg21514 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4850 sg5272

lemma sg21515 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5636

lemma sg21516 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5465

lemma sg21517 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5439

lemma sg21518 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4734 sg5597

lemma sg21519 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4737 sg5589

lemma sg21520 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4822 sg5358

lemma sg21521 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4734 sg5598

lemma sg21522 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4737 sg5590

lemma sg21523 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5485

lemma sg21524 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5637

lemma sg21525 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4723 sg5615

lemma sg21526 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,4,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5638

lemma sg21527 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4767 sg5524

lemma sg21528 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5466

lemma sg21529 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4719 sg5623

lemma sg21530 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg3935 sg6359

lemma sg21531 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,3,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4784 sg5486

lemma sg21532 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,3,3,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4718 sg5639

lemma sg21533 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,3,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg4860 sg5240

lemma sg21534 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4785 sg5483

lemma sg21535 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4784 sg5487

lemma sg21536 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5640

lemma sg21537 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4823 sg5357

lemma sg21538 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,4,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4785 sg5484

lemma sg21539 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,4,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5488

lemma sg21540 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5641

lemma sg21541 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,4,4,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5485

lemma sg21542 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5642

lemma sg21543 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,4,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5489

lemma sg21544 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4786 sg5483

lemma sg21545 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4822 sg5361

lemma sg21546 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5490

lemma sg21547 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5643

lemma sg21548 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4786 sg5484

lemma sg21549 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4851 sg5273

lemma sg21550 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5644

lemma sg21551 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5645

lemma sg21552 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5491

lemma sg21553 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4856 sg5259

lemma sg21554 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5646

lemma sg21555 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5492

lemma sg21556 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5493

lemma sg21557 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4851 sg5274

lemma sg21558 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4768 sg5524

lemma sg21559 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4787 sg5468

lemma sg21560 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4790 sg5441

lemma sg21561 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3935 sg6360

lemma sg21562 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,3,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4785 sg5486

lemma sg21563 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,3,3,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4784 sg5494

lemma sg21564 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,3,3,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5647

lemma sg21565 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,4,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4786 sg5486

lemma sg21566 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,4,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4785 sg5487

lemma sg21567 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,4,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5495

lemma sg21568 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,4,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5648

lemma sg21569 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,4,4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4823 sg5360

lemma sg21570 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,4,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5488

lemma sg21571 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,4,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5649

lemma sg21572 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,4,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5650

lemma sg21573 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,4,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5496

lemma sg21574 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4824 sg5359

lemma sg21575 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4786 sg5487

lemma sg21576 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5490

lemma sg21577 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5651

lemma sg21578 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5488

lemma sg21579 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5652

lemma sg21580 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5497

lemma sg21581 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5498

lemma sg21582 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,5,5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5653

lemma sg21583 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,6,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4824 sg5361

lemma sg21584 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,6,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5490

lemma sg21585 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,6,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5654

lemma sg21586 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,6,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5499

lemma sg21587 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,6,6,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5655

lemma sg21588 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4823 sg5362

lemma sg21589 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4785 sg5494

lemma sg21590 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4784 sg5500

lemma sg21591 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5656

lemma sg21592 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4824 sg5362

lemma sg21593 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4786 sg5494

lemma sg21594 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5495

lemma sg21595 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,4,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5657

lemma sg21596 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4853 sg5275

lemma sg21597 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5658

lemma sg21598 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4824 sg5363

lemma sg21599 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5495

lemma sg21600 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4718 sg5659

lemma sg21601 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,7,6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4854 sg5276

lemma sg21602 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,8,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4788 sg5466

lemma sg21603 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,8,3,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4823 sg5364

lemma sg21604 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,8,3,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4785 sg5500

lemma sg21605 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,8,4,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4824 sg5364

lemma sg21606 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,8,4,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4786 sg5500

lemma sg21607 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,9,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4828 sg5354

lemma sg21608 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,9,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4788 sg5468

lemma sg21609 : RowSquare [10,9,3,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg5506

lemma sg21610 : RowSquare [10,9,3,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg5505

lemma sg21611 : RowSquare [10,9,3,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg5504

lemma sg21612 : RowSquare [10,9,3,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg5503

lemma sg21613 : RowSquare [10,9,3,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4814 sg5502

lemma sg21614 : RowSquare [10,9,3,2,2,2,2,2,2,1] [2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4814 sg5501

lemma sg21615 : RowSquare [8,8,3,3,2,2,2,2,2,2,1,1] [6,5,5,5,5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg15266

lemma sg21616 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg20771

lemma sg21617 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg20772

lemma sg21618 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg20773

lemma sg21619 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg43 sg20774

lemma sg21620 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [6,3,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg43 sg20775

lemma sg21621 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [6,6,6,5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg15692

lemma sg21622 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg20770

lemma sg21623 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg20771

lemma sg21624 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg20772

lemma sg21625 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg20773

lemma sg21626 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg44 sg20774

lemma sg21627 : RowSquare [9,8,3,2,2,2,2,2,2,2,1,1] [7,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg44 sg20775

lemma sg21628 : RowSquare [10,8,2,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg21101

lemma sg21629 : RowSquare [10,8,2,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg21102

lemma sg21630 : RowSquare [10,8,2,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg21103

lemma sg21631 : RowSquare [10,8,2,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg21104

lemma sg21632 : RowSquare [10,8,2,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg15 sg21105

lemma sg21633 : RowSquare [10,8,2,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg21106

lemma sg21634 : RowSquare [10,9,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,4,4,4,4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3949 sg8009

lemma sg21635 : RowSquare [10,9,3,2,2,1,1,1,1,1,1,1,1,1,1] [5,5,5,5,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3952 sg8009

lemma sg21636 : RowSquare [10,9,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,4,4,4,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3956 sg8009

lemma sg21637 : RowSquare [11,9,2,2,2,2,2,2,2,1,1] [3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5671 sg5413

lemma sg21638 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg20776

lemma sg21639 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg20777

lemma sg21640 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg20778

lemma sg21641 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg20779

lemma sg21642 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg20780

lemma sg21643 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg80 sg20781

lemma sg21644 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,6,5,5,5,4] := by
  exact rowSquare_join (by decide) sg4782 sg7993

lemma sg21645 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,6,6,6,3,2,2] := by
  exact rowSquare_join (by decide) sg74 sg20784

lemma sg21646 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,6,6,6,4,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg20785

lemma sg21647 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,6,6,6,5,1,1] := by
  exact rowSquare_join (by decide) sg74 sg20786

lemma sg21648 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,6,6,6,5,2] := by
  exact rowSquare_join (by decide) sg74 sg20787

lemma sg21649 : RowSquare [9,8,3,3,2,2,2,2,2,2,1,1] [6,6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg74 sg20788

lemma sg21650 : RowSquare [9,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg21203

lemma sg21651 : RowSquare [9,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg21204

lemma sg21652 : RowSquare [9,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg21205

lemma sg21653 : RowSquare [9,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg21206

lemma sg21654 : RowSquare [9,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg21207

lemma sg21655 : RowSquare [9,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19 sg21208

lemma sg21656 : RowSquare [10,9,4,3,2,2,2,2,2,1] [10,10,3,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg5606 sg6122

lemma sg21657 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg21609

lemma sg21658 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg21610

lemma sg21659 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg21611

lemma sg21660 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg21612

lemma sg21661 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg21613

lemma sg21662 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [5,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg6 sg21614

lemma sg21663 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg21282

lemma sg21664 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg21283

lemma sg21665 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg21284

lemma sg21666 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg21285

lemma sg21667 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg12 sg21286

lemma sg21668 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg12 sg21287

lemma sg21669 : RowSquare [10,9,3,2,2,2,2,2,2,2,1,1] [6,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg12 sg21288

lemma sg21670 : RowSquare [11,9,3,2,2,2,2,2,2,2,1,1] [6,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3 sg21637

lemma sg21671 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [7,7,7,7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6410 sg6788

lemma sg21672 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [7,7,7,7,7,2,1,1] := by
  exact rowSquare_join (by decide) sg5509 sg8626

lemma sg21673 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,4,4,4,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg6151 sg7540

lemma sg21674 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7542

lemma sg21675 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,4,4,4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg6151 sg7543

lemma sg21676 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7545

lemma sg21677 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7546

lemma sg21678 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg6414 sg6768

lemma sg21679 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7547

lemma sg21680 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7548

lemma sg21681 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7549

lemma sg21682 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg6414 sg6769

lemma sg21683 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg5605 sg8409

lemma sg21684 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7550

lemma sg21685 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7551

lemma sg21686 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg6303 sg7303

lemma sg21687 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg6303 sg7304

lemma sg21688 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,4,4,3] := by
  exact rowSquare_join (by decide) sg5605 sg8410

lemma sg21689 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,5,2,2,2] := by
  exact rowSquare_join (by decide) sg6176 sg7492

lemma sg21690 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg6180 sg7486

lemma sg21691 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,5,3,3] := by
  exact rowSquare_join (by decide) sg4696 sg10842

lemma sg21692 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg6480 sg6629

lemma sg21693 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,5,4,2] := by
  exact rowSquare_join (by decide) sg4696 sg10843

lemma sg21694 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,5,5,5,5,5,5,1] := by
  exact rowSquare_join (by decide) sg4806 sg9652

lemma sg21695 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,4,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7553

lemma sg21696 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,4,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7554

lemma sg21697 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,4,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg6297 sg7316

lemma sg21698 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,4,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7556

lemma sg21699 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,4,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7557

lemma sg21700 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7558

lemma sg21701 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7317

lemma sg21702 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg6418 sg6768

lemma sg21703 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6151 sg7559

lemma sg21704 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7560

lemma sg21705 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7561

lemma sg21706 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7318

lemma sg21707 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7319

lemma sg21708 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,4,4,4,3] := by
  exact rowSquare_join (by decide) sg6418 sg6769

lemma sg21709 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7562

lemma sg21710 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6297 sg7320

lemma sg21711 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7563

lemma sg21712 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6297 sg7321

lemma sg21713 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,4,3,3] := by
  exact rowSquare_join (by decide) sg6305 sg7303

lemma sg21714 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6632

lemma sg21715 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,4,4,2] := by
  exact rowSquare_join (by decide) sg6305 sg7304

lemma sg21716 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg6177 sg7492

lemma sg21717 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg6473 sg6633

lemma sg21718 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,5,3,2] := by
  exact rowSquare_join (by decide) sg6182 sg7486

lemma sg21719 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,5,5,5,5,4,1] := by
  exact rowSquare_join (by decide) sg6482 sg6629

lemma sg21720 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,4,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg6176 sg7494

lemma sg21721 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,4,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7564

lemma sg21722 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7565

lemma sg21723 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg6414 sg6779

lemma sg21724 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6780

lemma sg21725 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,4,4,4,4,3] := by
  exact rowSquare_join (by decide) sg6423 sg6768

lemma sg21726 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg6151 sg7566

lemma sg21727 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7567

lemma sg21728 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg6414 sg6782

lemma sg21729 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7568

lemma sg21730 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6783

lemma sg21731 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,4,4,3,3] := by
  exact rowSquare_join (by decide) sg6425 sg6768

lemma sg21732 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6650

lemma sg21733 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,4,4,4,2] := by
  exact rowSquare_join (by decide) sg6154 sg7546

lemma sg21734 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg6151 sg7569

lemma sg21735 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg6414 sg6784

lemma sg21736 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,3,3,3] := by
  exact rowSquare_join (by decide) sg6426 sg6768

lemma sg21737 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg6303 sg7313

lemma sg21738 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg6472 sg6652

lemma sg21739 : RowSquare [11,9,4,3,2,2,2,2,2,1,1] [8,6,6,5,5,4,3,2] := by
  exact rowSquare_join (by decide) sg6475 sg6631

end UniversalTensorSquare
end
end

end OAI
