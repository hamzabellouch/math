import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes10

namespace OAI

/-! Semigroup Nodes 12. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5327 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg709

lemma sg5328 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,3,2,2] := by
  exact rowSquare_join (by decide) sg413 sg1007

lemma sg5329 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,3,3,1] := by
  exact rowSquare_join (by decide) sg590 sg709

lemma sg5330 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg710

lemma sg5331 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,4,4,2,1] := by
  exact rowSquare_join (by decide) sg590 sg710

lemma sg5332 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg418 sg998

lemma sg5333 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg418 sg999

lemma sg5334 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg414 sg1006

lemma sg5335 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,5,2,2,2] := by
  exact rowSquare_join (by decide) sg418 sg1001

lemma sg5336 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg415 sg1006

lemma sg5337 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,5,3,2,1] := by
  exact rowSquare_join (by decide) sg414 sg1007

lemma sg5338 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,5,3,3] := by
  exact rowSquare_join (by decide) sg414 sg1008

lemma sg5339 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,5,4,1,1] := by
  exact rowSquare_join (by decide) sg415 sg1007

lemma sg5340 : RowSquare [5,3,1,1,1,1,1,1,1,1,1,1] [7,5,4,2] := by
  exact rowSquare_join (by decide) sg415 sg1008

lemma sg5341 : RowSquare [5,3,2,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg389 sg998

lemma sg5342 : RowSquare [5,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg998

lemma sg5343 : RowSquare [5,3,2,1,1,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg696

lemma sg5344 : RowSquare [5,3,2,1,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg413 sg910

lemma sg5345 : RowSquare [5,3,2,1,1,1,1,1,1,1,1] [5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg414 sg910

lemma sg5346 : RowSquare [5,3,2,1,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg415 sg910

lemma sg5347 : RowSquare [5,3,2,2,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg389 sg910

lemma sg5348 : RowSquare [5,3,2,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg390 sg910

lemma sg5349 : RowSquare [5,3,2,2,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg646

lemma sg5350 : RowSquare [5,3,2,2,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg647

lemma sg5351 : RowSquare [5,3,2,2,1,1,1,1,1,1] [5,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg1682

lemma sg5352 : RowSquare [5,3,2,2,1,1,1,1,1,1] [5,3,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg1682

lemma sg5353 : RowSquare [5,3,2,2,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg649

lemma sg5354 : RowSquare [5,3,2,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg396 sg910

lemma sg5355 : RowSquare [5,3,2,2,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg650

lemma sg5356 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg106 sg1682

lemma sg5357 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg397 sg910

lemma sg5358 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg651

lemma sg5359 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg398 sg910

lemma sg5360 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg652

lemma sg5361 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg653

lemma sg5362 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg399 sg910

lemma sg5363 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg654

lemma sg5364 : RowSquare [5,3,2,2,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg655

lemma sg5365 : RowSquare [5,3,3,2,1,1,1,1,1] [4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg2137

lemma sg5366 : RowSquare [5,3,3,2,1,1,1,1,1] [4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg2137

lemma sg5367 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg673

lemma sg5368 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg674

lemma sg5369 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg998

lemma sg5370 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg675

lemma sg5371 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg676

lemma sg5372 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg370 sg1000

lemma sg5373 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg370 sg1001

lemma sg5374 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg998

lemma sg5375 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg372 sg998

lemma sg5376 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg998

lemma sg5377 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg371 sg1000

lemma sg5378 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg371 sg1001

lemma sg5379 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg372 sg1000

lemma sg5380 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg372 sg1001

lemma sg5381 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg373 sg1000

lemma sg5382 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg373 sg1001

lemma sg5383 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg677

lemma sg5384 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg673

lemma sg5385 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg678

lemma sg5386 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg674

lemma sg5387 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,3,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg679

lemma sg5388 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,3,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg675

lemma sg5389 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg676

lemma sg5390 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg374 sg1000

lemma sg5391 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg374 sg1001

lemma sg5392 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,4,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg680

lemma sg5393 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,4,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg375 sg998

lemma sg5394 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg681

lemma sg5395 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,4,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg376 sg998

lemma sg5396 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg375 sg1001

lemma sg5397 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg377 sg998

lemma sg5398 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg1006

lemma sg5399 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg682

lemma sg5400 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg677

lemma sg5401 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg683

lemma sg5402 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg678

lemma sg5403 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg684

lemma sg5404 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg679

lemma sg5405 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg379 sg1001

lemma sg5406 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,4,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg685

lemma sg5407 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,4,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg680

lemma sg5408 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,4,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg681

lemma sg5409 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg686

lemma sg5410 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,5,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg382 sg998

lemma sg5411 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg998

lemma sg5412 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg383 sg1001

lemma sg5413 : RowSquare [5,4,1,1,1,1,1,1,1,1,1] [10,4,4] := by
  exact rowSquare_join (by decide) sg4 sg3162

lemma sg5414 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg370 sg910

lemma sg5415 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg613

lemma sg5416 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg910

lemma sg5417 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg998

lemma sg5418 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg372 sg910

lemma sg5419 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg615

lemma sg5420 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg999

lemma sg5421 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg373 sg910

lemma sg5422 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1000

lemma sg5423 : RowSquare [5,4,2,1,1,1,1,1,1,1] [3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1001

lemma sg5424 : RowSquare [5,4,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg374 sg910

lemma sg5425 : RowSquare [5,4,2,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg617

lemma sg5426 : RowSquare [5,4,2,1,1,1,1,1,1,1] [4,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg376 sg910

lemma sg5427 : RowSquare [5,4,2,1,1,1,1,1,1,1] [4,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg613 sg589

lemma sg5428 : RowSquare [5,4,2,1,1,1,1,1,1,1] [4,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg378 sg910

lemma sg5429 : RowSquare [5,4,2,1,1,1,1,1,1,1] [4,4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg623

lemma sg5430 : RowSquare [5,4,2,1,1,1,1,1,1,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg615 sg589

lemma sg5431 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg379 sg910

lemma sg5432 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg624

lemma sg5433 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg4674

lemma sg5434 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,3,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg380 sg910

lemma sg5435 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg381 sg910

lemma sg5436 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg4675

lemma sg5437 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,3,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg4676

lemma sg5438 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg4677

lemma sg5439 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg4678

lemma sg5440 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg0 sg4684

lemma sg5441 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg383 sg910

lemma sg5442 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg628

lemma sg5443 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg371 sg920

lemma sg5444 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1016

lemma sg5445 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg623

lemma sg5446 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg615 sg596

lemma sg5447 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,4,4] := by
  exact rowSquare_join (by decide) sg373 sg922

lemma sg5448 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,5,1,1,1] := by
  exact rowSquare_join (by decide) sg589 sg623

lemma sg5449 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg590 sg623

lemma sg5450 : RowSquare [5,4,2,1,1,1,1,1,1,1] [5,5,5,3] := by
  exact rowSquare_join (by decide) sg373 sg923

lemma sg5451 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg384 sg910

lemma sg5452 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg629

lemma sg5453 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg4685

lemma sg5454 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg4686

lemma sg5455 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg385 sg910

lemma sg5456 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg630

lemma sg5457 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg4687

lemma sg5458 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg4688

lemma sg5459 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg631

lemma sg5460 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg4689

lemma sg5461 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3832

lemma sg5462 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg4690

lemma sg5463 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3833

lemma sg5464 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg1 sg3834

lemma sg5465 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg3835

lemma sg5466 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,4,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg386 sg910

lemma sg5467 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg3839

lemma sg5468 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg632

lemma sg5469 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,5,4,2,1] := by
  exact rowSquare_join (by decide) sg4 sg3165

lemma sg5470 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,5,4,3] := by
  exact rowSquare_join (by decide) sg4 sg3166

lemma sg5471 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3167

lemma sg5472 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,5,5,2] := by
  exact rowSquare_join (by decide) sg4 sg3168

lemma sg5473 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg1023

lemma sg5474 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg371 sg931

lemma sg5475 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg621 sg595

lemma sg5476 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,3,1,1,1] := by
  exact rowSquare_join (by decide) sg615 sg602

lemma sg5477 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,3,2,1] := by
  exact rowSquare_join (by decide) sg4 sg3169

lemma sg5478 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,3,3] := by
  exact rowSquare_join (by decide) sg373 sg931

lemma sg5479 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3170

lemma sg5480 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,4,2] := by
  exact rowSquare_join (by decide) sg4 sg3171

lemma sg5481 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,5,1] := by
  exact rowSquare_join (by decide) sg4 sg3172

lemma sg5482 : RowSquare [5,4,2,1,1,1,1,1,1,1] [6,6,6] := by
  exact rowSquare_join (by decide) sg4 sg3173

lemma sg5483 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg387 sg910

lemma sg5484 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg633

lemma sg5485 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3840

lemma sg5486 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg388 sg910

lemma sg5487 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg634

lemma sg5488 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3841

lemma sg5489 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg3842

lemma sg5490 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3843

lemma sg5491 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg3174

lemma sg5492 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3844

lemma sg5493 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,3,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg3845

lemma sg5494 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg635

lemma sg5495 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg4693

lemma sg5496 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg3846

lemma sg5497 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3175

lemma sg5498 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,4,3,2,2] := by
  exact rowSquare_join (by decide) sg4 sg3176

lemma sg5499 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3177

lemma sg5500 : RowSquare [5,4,2,1,1,1,1,1,1,1] [7,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg4695

lemma sg5501 : RowSquare [5,4,2,1,1,1,1,1,1,1] [9,9] := by
  exact rowSquare_join (by decide) sg14 sg2490

lemma sg5502 : RowSquare [5,4,2,1,1,1,1,1,1,1] [10,8] := by
  exact rowSquare_join (by decide) sg42 sg2014

lemma sg5503 : RowSquare [5,4,2,1,1,1,1,1,1,1] [11,7] := by
  exact rowSquare_join (by decide) sg80 sg1577

lemma sg5504 : RowSquare [5,4,2,1,1,1,1,1,1,1] [12,6] := by
  exact rowSquare_join (by decide) sg80 sg1578

lemma sg5505 : RowSquare [5,4,2,1,1,1,1,1,1,1] [13,5] := by
  exact rowSquare_join (by decide) sg174 sg1120

lemma sg5506 : RowSquare [5,4,2,1,1,1,1,1,1,1] [14,4] := by
  exact rowSquare_join (by decide) sg363 sg718

lemma sg5507 : RowSquare [5,4,2,2,1,1,1,1,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg330 sg910

lemma sg5508 : RowSquare [5,4,2,2,1,1,1,1,1] [3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg912

lemma sg5509 : RowSquare [5,4,2,2,1,1,1,1,1] [3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg915

lemma sg5510 : RowSquare [5,4,2,2,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2596

lemma sg5511 : RowSquare [5,4,2,2,1,1,1,1,1] [6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2597

lemma sg5512 : RowSquare [5,4,2,2,1,1,1,1,1] [6,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg2598

lemma sg5513 : RowSquare [5,4,2,2,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg4697

lemma sg5514 : RowSquare [5,4,2,2,1,1,1,1,1] [8,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg4698

lemma sg5515 : RowSquare [5,4,2,2,2,2,1] [5,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg2596

lemma sg5516 : RowSquare [5,4,2,2,2,2,1] [5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2603

lemma sg5517 : RowSquare [5,4,2,2,2,2,1] [5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2607

lemma sg5518 : RowSquare [5,4,2,2,2,2,1] [5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2608

lemma sg5519 : RowSquare [5,4,2,2,2,2,1] [6,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg2597

lemma sg5520 : RowSquare [5,4,2,2,2,2,1] [6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg2601

lemma sg5521 : RowSquare [5,4,2,2,2,2,1] [6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg15 sg2602

lemma sg5522 : RowSquare [5,4,2,2,2,2,1] [6,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2611

lemma sg5523 : RowSquare [5,4,2,2,2,2,1] [6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg302 sg838

lemma sg5524 : RowSquare [5,4,3,2,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg3299

lemma sg5525 : RowSquare [5,5,1,1,1,1,1,1,1,1] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg586 sg586

lemma sg5526 : RowSquare [5,5,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg587

lemma sg5527 : RowSquare [5,5,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg588

lemma sg5528 : RowSquare [5,5,1,1,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg589

lemma sg5529 : RowSquare [5,5,1,1,1,1,1,1,1,1] [3,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg590

lemma sg5530 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg586 sg591

lemma sg5531 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg587

lemma sg5532 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg593

lemma sg5533 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg312 sg999

lemma sg5534 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg594

lemma sg5535 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg312 sg1000

lemma sg5536 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg595

lemma sg5537 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg313 sg998

lemma sg5538 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg588

lemma sg5539 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg596

lemma sg5540 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg314 sg998

lemma sg5541 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg589

lemma sg5542 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg998

lemma sg5543 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg590

lemma sg5544 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg313 sg1000

lemma sg5545 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg313 sg1001

lemma sg5546 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg314 sg999

lemma sg5547 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg589

lemma sg5548 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg999

lemma sg5549 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg589 sg590

lemma sg5550 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,3,3] := by
  exact rowSquare_join (by decide) sg314 sg1001

lemma sg5551 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1000

lemma sg5552 : RowSquare [5,5,1,1,1,1,1,1,1,1] [4,4,4,4,2] := by
  exact rowSquare_join (by decide) sg590 sg590

lemma sg5553 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg597

lemma sg5554 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg587 sg591

lemma sg5555 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg592

lemma sg5556 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg588 sg591

lemma sg5557 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg591 sg589

lemma sg5558 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg594

lemma sg5559 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg316 sg1000

lemma sg5560 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg316 sg1001

lemma sg5561 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,4,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg588 sg592

lemma sg5562 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,4,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg601

lemma sg5563 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg589 sg592

lemma sg5564 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg594

lemma sg5565 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,4,4,4,1] := by
  exact rowSquare_join (by decide) sg590 sg594

lemma sg5566 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg602

lemma sg5567 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg319 sg998

lemma sg5568 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg588 sg595

lemma sg5569 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,2,2,2,2] := by
  exact rowSquare_join (by decide) sg313 sg1006

lemma sg5570 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg320 sg998

lemma sg5571 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg588 sg596

lemma sg5572 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,3,3,1,1] := by
  exact rowSquare_join (by decide) sg313 sg1008

lemma sg5573 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg590 sg595

lemma sg5574 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg320 sg999

lemma sg5575 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg589 sg596

lemma sg5576 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg314 sg1007

lemma sg5577 : RowSquare [5,5,1,1,1,1,1,1,1,1] [5,5,4,4] := by
  exact rowSquare_join (by decide) sg315 sg1008

lemma sg5578 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg603

lemma sg5579 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg587 sg597

lemma sg5580 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg3866

lemma sg5581 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3869

lemma sg5582 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,4,4,4] := by
  exact rowSquare_join (by decide) sg1 sg3875

lemma sg5583 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,6,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg998

lemma sg5584 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,6,2,2,1,1] := by
  exact rowSquare_join (by decide) sg313 sg1015

lemma sg5585 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,6,2,2,2] := by
  exact rowSquare_join (by decide) sg595 sg595

lemma sg5586 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,6,3,3] := by
  exact rowSquare_join (by decide) sg315 sg1015

lemma sg5587 : RowSquare [5,5,1,1,1,1,1,1,1,1] [6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg314 sg1016

lemma sg5588 : RowSquare [5,5,1,1,1,1,1,1,1,1] [7,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg608

lemma sg5589 : RowSquare [5,5,1,1,1,1,1,1,1,1] [7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg603

lemma sg5590 : RowSquare [5,5,1,1,1,1,1,1,1,1] [7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg3876

lemma sg5591 : RowSquare [5,5,1,1,1,1,1,1,1,1] [7,5,5,1] := by
  exact rowSquare_join (by decide) sg13 sg2497

lemma sg5592 : RowSquare [5,5,1,1,1,1,1,1,1,1] [7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg1023

lemma sg5593 : RowSquare [5,5,1,1,1,1,1,1,1,1] [7,7,2,2] := by
  exact rowSquare_join (by decide) sg315 sg1023

lemma sg5594 : RowSquare [5,5,1,1,1,1,1,1,1,1] [7,7,4] := by
  exact rowSquare_join (by decide) sg320 sg1016

lemma sg5595 : RowSquare [5,5,1,1,1,1,1,1,1,1] [8,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg611

lemma sg5596 : RowSquare [5,5,1,1,1,1,1,1,1,1] [8,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg587 sg608

lemma sg5597 : RowSquare [5,5,1,1,1,1,1,1,1,1] [8,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3896

lemma sg5598 : RowSquare [5,5,1,1,1,1,1,1,1,1] [8,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg3897

lemma sg5599 : RowSquare [5,5,1,1,1,1,1,1,1,1] [8,8,1,1] := by
  exact rowSquare_join (by decide) sg319 sg1023

lemma sg5600 : RowSquare [5,5,1,1,1,1,1,1,1,1] [9,9] := by
  exact rowSquare_join (by decide) sg324 sg1023

lemma sg5601 : RowSquare [5,5,2,1,1,1,1,1,1] [3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg313 sg910

lemma sg5602 : RowSquare [5,5,2,1,1,1,1,1,1] [3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg314 sg910

lemma sg5603 : RowSquare [5,5,2,1,1,1,1,1,1] [3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg586 sg536

lemma sg5604 : RowSquare [5,5,2,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg910

lemma sg5605 : RowSquare [5,5,2,1,1,1,1,1,1] [4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg587 sg534

lemma sg5606 : RowSquare [5,5,2,1,1,1,1,1,1] [5,5,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg324 sg910

lemma sg5607 : RowSquare [5,5,2,2,2,1,1] [4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg3999

lemma sg5608 : RowSquare [5,5,2,2,2,1,1] [4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg4002

lemma sg5609 : RowSquare [5,5,2,2,2,1,1] [4,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg4003

lemma sg5610 : RowSquare [5,5,2,2,2,1,1] [4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg4004

lemma sg5611 : RowSquare [5,5,2,2,2,1,1] [4,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg4005

lemma sg5612 : RowSquare [5,5,2,2,2,1,1] [5,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg4009

lemma sg5613 : RowSquare [5,5,2,2,2,1,1] [5,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg4010

lemma sg5614 : RowSquare [5,5,2,2,2,1,1] [5,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg4011

lemma sg5615 : RowSquare [6,4,1,1,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg1327

lemma sg5616 : RowSquare [6,4,1,1,1,1,1,1,1,1] [3,3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg1327

lemma sg5617 : RowSquare [6,4,1,1,1,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg182 sg1327

lemma sg5618 : RowSquare [6,4,1,1,1,1,1,1,1,1] [4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg183 sg1327

lemma sg5619 : RowSquare [6,4,1,1,1,1,1,1,1,1] [4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg184 sg1327

lemma sg5620 : RowSquare [6,4,1,1,1,1,1,1,1,1] [4,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg179 sg1332

lemma sg5621 : RowSquare [6,4,1,1,1,1,1,1,1,1] [5,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg186 sg1327

lemma sg5622 : RowSquare [6,4,1,1,1,1,1,1,1,1] [5,3,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg187 sg1327

lemma sg5623 : RowSquare [6,4,1,1,1,1,1,1,1,1] [5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg188 sg1327

lemma sg5624 : RowSquare [6,4,1,1,1,1,1,1,1,1] [6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3187

lemma sg5625 : RowSquare [6,4,1,1,1,1,1,1,1,1] [6,5,5,2] := by
  exact rowSquare_join (by decide) sg4 sg3188

lemma sg5626 : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,5,5,1] := by
  exact rowSquare_join (by decide) sg4 sg3190

lemma sg5627 : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,6,4,1] := by
  exact rowSquare_join (by decide) sg4 sg3191

lemma sg5628 : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,6,5] := by
  exact rowSquare_join (by decide) sg4 sg3192

lemma sg5629 : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,7,1,1,1,1] := by
  exact rowSquare_join (by decide) sg371 sg909

lemma sg5630 : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,7,2,1,1] := by
  exact rowSquare_join (by decide) sg372 sg909

lemma sg5631 : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,7,2,2] := by
  exact rowSquare_join (by decide) sg373 sg909

lemma sg5632 : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,7,3,1] := by
  exact rowSquare_join (by decide) sg377 sg903

lemma sg5633 : RowSquare [6,4,1,1,1,1,1,1,1,1] [7,7,4] := by
  exact rowSquare_join (by decide) sg378 sg903

lemma sg5634 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg191 sg1328

lemma sg5635 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3945

lemma sg5636 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2511

lemma sg5637 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg3186

lemma sg5638 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg2 sg3897

lemma sg5639 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3946

lemma sg5640 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3193

lemma sg5641 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2512

lemma sg5642 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg3189

lemma sg5643 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3194

lemma sg5644 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2513

lemma sg5645 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,3,3,2,2] := by
  exact rowSquare_join (by decide) sg16 sg2495

lemma sg5646 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg2514

lemma sg5647 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3947

lemma sg5648 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2508

lemma sg5649 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2515

lemma sg5650 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,4,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg2495

lemma sg5651 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3195

lemma sg5652 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg2516

lemma sg5653 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg2517

lemma sg5654 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,4,4,1,1] := by
  exact rowSquare_join (by decide) sg16 sg2496

lemma sg5655 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,4,4,2] := by
  exact rowSquare_join (by decide) sg13 sg2518

lemma sg5656 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2509

lemma sg5657 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2510

lemma sg5658 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg2519

lemma sg5659 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,5,3,1,1] := by
  exact rowSquare_join (by decide) sg17 sg2496

lemma sg5660 : RowSquare [6,4,1,1,1,1,1,1,1,1] [8,5,5] := by
  exact rowSquare_join (by decide) sg16 sg2497

lemma sg5661 : RowSquare [6,4,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg330 sg889

lemma sg5662 : RowSquare [6,4,2,1,1,1,1,1,1] [3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg330 sg890

lemma sg5663 : RowSquare [6,4,2,1,1,1,1,1,1] [3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg330 sg892

lemma sg5664 : RowSquare [6,4,2,1,1,1,1,1,1] [4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg1754

lemma sg5665 : RowSquare [6,4,2,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3957

lemma sg5666 : RowSquare [6,4,2,1,1,1,1,1,1] [7,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg153 sg1327

lemma sg5667 : RowSquare [6,4,2,1,1,1,1,1,1] [7,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3198

lemma sg5668 : RowSquare [6,4,2,1,1,1,1,1,1] [7,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3958

lemma sg5669 : RowSquare [6,4,3,1,1,1,1,1] [3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg1196

lemma sg5670 : RowSquare [6,4,3,2,2,1] [3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg74 sg1616

lemma sg5671 : RowSquare [6,5,1,1,1,1,1,1,1] [8,5,5] := by
  exact rowSquare_join (by decide) sg83 sg1583

lemma sg5673 : RowSquare [6,5,2,2,2,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg508 sg474

lemma sg5674 : RowSquare [6,5,2,2,2,1] [2,2,2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg506 sg474

lemma sg5675 : RowSquare [6,5,2,2,2,1] [2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg503 sg473

lemma sg5676 : RowSquare [6,5,2,2,2,1] [2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg503 sg472

lemma sg5677 : RowSquare [6,5,2,2,2,1] [2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg503 sg471

lemma sg5678 : RowSquare [6,5,2,2,2,1] [2,2,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg503 sg470

lemma sg5679 : RowSquare [6,5,2,2,2,1] [2,2,2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg281 sg780

lemma sg5680 : RowSquare [6,5,2,2,2,1] [3,2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg505 sg474

lemma sg5681 : RowSquare [6,5,2,2,2,1] [3,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg500 sg473

lemma sg5682 : RowSquare [6,5,2,2,2,1] [3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg500 sg472

lemma sg5683 : RowSquare [6,5,2,2,2,1] [3,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg500 sg471

lemma sg5684 : RowSquare [6,5,2,2,2,1] [3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg500 sg470

lemma sg5685 : RowSquare [6,5,2,2,2,1] [3,3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg502 sg474

lemma sg5686 : RowSquare [6,5,2,2,2,1] [3,3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg499 sg474

lemma sg5687 : RowSquare [6,5,2,2,2,1] [3,3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg499 sg472

lemma sg5688 : RowSquare [6,5,2,2,2,1] [3,3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg499 sg471

lemma sg5689 : RowSquare [6,5,2,2,2,1] [3,3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg499 sg470

lemma sg5690 : RowSquare [6,5,2,2,2,1] [3,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg500 sg465

lemma sg5691 : RowSquare [6,5,2,2,2,1] [3,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg496 sg472

lemma sg5692 : RowSquare [6,5,2,2,2,1] [3,3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg496 sg471

lemma sg5693 : RowSquare [6,5,2,2,2,1] [3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg496 sg470

lemma sg5694 : RowSquare [6,5,2,2,2,1] [3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg496 sg468

lemma sg5695 : RowSquare [6,5,2,2,2,1] [3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg496 sg464

lemma sg5696 : RowSquare [6,5,2,2,2,1] [3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg496 sg459

lemma sg5697 : RowSquare [6,5,2,2,2,1] [4,3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg498 sg474

lemma sg5698 : RowSquare [6,5,2,2,2,1] [4,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg495 sg473

lemma sg5699 : RowSquare [6,5,2,2,2,1] [4,3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg495 sg472

lemma sg5700 : RowSquare [6,5,2,2,2,1] [4,3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg495 sg471

lemma sg5701 : RowSquare [6,5,2,2,2,1] [4,3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg495 sg470

lemma sg5702 : RowSquare [6,5,2,2,2,1] [4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg493 sg474

lemma sg5703 : RowSquare [6,5,2,2,2,1] [4,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg493 sg473

lemma sg5704 : RowSquare [6,5,2,2,2,1] [4,4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg493 sg470

lemma sg5705 : RowSquare [6,5,2,2,2,1] [4,4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg493 sg469

lemma sg5706 : RowSquare [6,5,2,2,2,1] [5,4,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg490 sg474

lemma sg5707 : RowSquare [6,5,2,2,2,1] [7,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg3243

lemma sg5708 : RowSquare [6,5,2,2,2,1] [7,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg3244

lemma sg5709 : RowSquare [6,5,2,2,2,1] [7,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3246

lemma sg5710 : RowSquare [6,5,2,2,2,1] [7,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg2544

lemma sg5711 : RowSquare [6,5,2,2,2,1] [7,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3989

lemma sg5712 : RowSquare [6,5,2,2,2,1] [7,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg3990

lemma sg5713 : RowSquare [6,5,2,2,2,1] [7,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2543

lemma sg5714 : RowSquare [6,5,2,2,2,1] [7,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3247

lemma sg5715 : RowSquare [6,5,2,2,2,1] [7,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg838

lemma sg5716 : RowSquare [6,5,2,2,2,1] [7,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg3991

lemma sg5717 : RowSquare [6,5,2,2,2,1] [7,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg239 sg842

lemma sg5718 : RowSquare [6,5,2,2,2,1] [7,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg839

lemma sg5719 : RowSquare [6,5,2,2,2,1] [7,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg3245

lemma sg5720 : RowSquare [6,5,2,2,2,1] [7,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg240 sg842

lemma sg5721 : RowSquare [6,5,2,2,2,1] [7,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg116 sg1206

lemma sg5722 : RowSquare [6,5,2,2,2,1] [7,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg241 sg842

lemma sg5723 : RowSquare [6,5,2,2,2,1] [8,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg6 sg3244

lemma sg5724 : RowSquare [6,5,2,2,2,1] [8,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg3246

lemma sg5725 : RowSquare [6,5,2,2,2,1] [8,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg3248

lemma sg5726 : RowSquare [6,5,2,2,2,1] [8,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg242 sg842

lemma sg5727 : RowSquare [6,5,2,2,2,1] [8,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg2544

end UniversalTensorSquare
end
end

end OAI
