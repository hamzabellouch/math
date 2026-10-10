import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes32
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes37

namespace OAI

/-! Semigroup Nodes 47. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg19340 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg165 sg11609

lemma sg19341 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14278

lemma sg19342 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,2,2,1] := by
  exact rowSquare_join (by decide) sg84 sg12510

lemma sg19343 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12511

lemma sg19344 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,2] := by
  exact rowSquare_join (by decide) sg84 sg12512

lemma sg19345 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg84 sg12513

lemma sg19346 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,5] := by
  exact rowSquare_join (by decide) sg84 sg12514

lemma sg19347 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14215

lemma sg19348 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg3546 sg4169

lemma sg19349 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg14216

lemma sg19350 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14217

lemma sg19351 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3314 sg4431

lemma sg19352 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14279

lemma sg19353 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14280

lemma sg19354 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14281

lemma sg19355 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14282

lemma sg19356 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14218

lemma sg19357 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg3539 sg4179

lemma sg19358 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg3539 sg4180

lemma sg19359 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg26 sg12877

lemma sg19360 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg83 sg12519

lemma sg19361 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14219

lemma sg19362 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11610

lemma sg19363 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg26 sg12879

lemma sg19364 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14283

lemma sg19365 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14284

lemma sg19366 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11611

lemma sg19367 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14222

lemma sg19368 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11612

lemma sg19369 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,4,3] := by
  exact rowSquare_join (by decide) sg3540 sg4180

lemma sg19370 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14285

lemma sg19371 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14286

lemma sg19372 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14287

lemma sg19373 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11613

lemma sg19374 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14288

lemma sg19375 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg165 sg11614

lemma sg19376 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,5,1] := by
  exact rowSquare_join (by decide) sg165 sg11615

lemma sg19377 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11616

lemma sg19378 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12520

lemma sg19379 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg166 sg11605

lemma sg19380 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11617

lemma sg19381 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11606

lemma sg19382 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg165 sg11618

lemma sg19383 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12884

lemma sg19384 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg26 sg12885

lemma sg19385 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12886

lemma sg19386 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,2] := by
  exact rowSquare_join (by decide) sg166 sg11607

lemma sg19387 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,4,1] := by
  exact rowSquare_join (by decide) sg166 sg11608

lemma sg19388 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,5] := by
  exact rowSquare_join (by decide) sg166 sg11609

lemma sg19389 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14289

lemma sg19390 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14290

lemma sg19391 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14291

lemma sg19392 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14292

lemma sg19393 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg13 sg14293

lemma sg19394 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14294

lemma sg19395 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14235

lemma sg19396 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg14 sg14236

lemma sg19397 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg83 sg12526

lemma sg19398 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14295

lemma sg19399 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg166 sg11611

lemma sg19400 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg14296

lemma sg19401 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11612

lemma sg19402 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,4,4,2] := by
  exact rowSquare_join (by decide) sg14 sg14243

lemma sg19403 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14297

lemma sg19404 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14298

lemma sg19405 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14299

lemma sg19406 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,5,3,2] := by
  exact rowSquare_join (by decide) sg166 sg11613

lemma sg19407 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,5,4,1] := by
  exact rowSquare_join (by decide) sg166 sg11614

lemma sg19408 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,5,5] := by
  exact rowSquare_join (by decide) sg166 sg11615

lemma sg19409 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12527

lemma sg19410 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg166 sg11616

lemma sg19411 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,3,3,3] := by
  exact rowSquare_join (by decide) sg83 sg12528

lemma sg19412 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12529

lemma sg19413 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg167 sg11611

lemma sg19414 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11612

lemma sg19415 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,4,3,2] := by
  exact rowSquare_join (by decide) sg166 sg11617

lemma sg19416 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,4,4,1] := by
  exact rowSquare_join (by decide) sg166 sg11618

lemma sg19417 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14300

lemma sg19418 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14301

lemma sg19419 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,5,2,2] := by
  exact rowSquare_join (by decide) sg167 sg11613

lemma sg19420 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,5,3,1] := by
  exact rowSquare_join (by decide) sg167 sg11614

lemma sg19421 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,5,4] := by
  exact rowSquare_join (by decide) sg167 sg11615

lemma sg19422 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14302

lemma sg19423 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,6,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14303

lemma sg19424 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,6,6,3] := by
  exact rowSquare_join (by decide) sg13 sg14304

lemma sg19425 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3537 sg4183

lemma sg19426 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15137

lemma sg19427 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11628

lemma sg19428 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12518

lemma sg19429 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11629

lemma sg19430 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,4,3] := by
  exact rowSquare_join (by decide) sg1 sg15138

lemma sg19431 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15139

lemma sg19432 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,5,5,2] := by
  exact rowSquare_join (by decide) sg1 sg15140

lemma sg19433 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15141

lemma sg19434 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,4,4,4,4] := by
  exact rowSquare_join (by decide) sg391 sg11553

lemma sg19435 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11636

lemma sg19436 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11627

lemma sg19437 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11637

lemma sg19438 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg15142

lemma sg19439 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12520

lemma sg19440 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,2,1] := by
  exact rowSquare_join (by decide) sg166 sg11628

lemma sg19441 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11638

lemma sg19442 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11629

lemma sg19443 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,4,2] := by
  exact rowSquare_join (by decide) sg165 sg11639

lemma sg19444 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,5,5,5,1] := by
  exact rowSquare_join (by decide) sg165 sg11640

lemma sg19445 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11642

lemma sg19446 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11627

lemma sg19447 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11644

lemma sg19448 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11645

lemma sg19449 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,1,1] := by
  exact rowSquare_join (by decide) sg168 sg11606

lemma sg19450 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,4,2] := by
  exact rowSquare_join (by decide) sg165 sg11646

lemma sg19451 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12522

lemma sg19452 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,2,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11647

lemma sg19453 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11629

lemma sg19454 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11648

lemma sg19455 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,4,1] := by
  exact rowSquare_join (by decide) sg165 sg11649

lemma sg19456 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,5,5] := by
  exact rowSquare_join (by decide) sg168 sg11609

lemma sg19457 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12523

lemma sg19458 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12524

lemma sg19459 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,2,2] := by
  exact rowSquare_join (by decide) sg165 sg11650

lemma sg19460 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11651

lemma sg19461 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,6,4] := by
  exact rowSquare_join (by decide) sg84 sg12525

lemma sg19462 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11655

lemma sg19463 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11633

lemma sg19464 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11656

lemma sg19465 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,4,4,4,3] := by
  exact rowSquare_join (by decide) sg1 sg15143

lemma sg19466 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11658

lemma sg19467 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11633

lemma sg19468 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11660

lemma sg19469 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11661

lemma sg19470 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11637

lemma sg19471 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,4,4,2] := by
  exact rowSquare_join (by decide) sg165 sg11662

lemma sg19472 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12529

lemma sg19473 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11663

lemma sg19474 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12530

lemma sg19475 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11664

lemma sg19476 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,4,1] := by
  exact rowSquare_join (by decide) sg165 sg11665

lemma sg19477 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,5,5,5] := by
  exact rowSquare_join (by decide) sg166 sg11640

lemma sg19478 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11641

lemma sg19479 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11666

lemma sg19480 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,3,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11667

lemma sg19481 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11643

lemma sg19482 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,2,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11668

lemma sg19483 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11644

lemma sg19484 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11669

lemma sg19485 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,4,4,1] := by
  exact rowSquare_join (by decide) sg165 sg11670

lemma sg19486 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12531

lemma sg19487 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11647

lemma sg19488 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,2,2] := by
  exact rowSquare_join (by decide) sg165 sg11671

lemma sg19489 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11672

lemma sg19490 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,5,4] := by
  exact rowSquare_join (by decide) sg166 sg11649

lemma sg19491 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,6,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12532

lemma sg19492 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,6,2,1] := by
  exact rowSquare_join (by decide) sg166 sg11650

lemma sg19493 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,7,6,6,3] := by
  exact rowSquare_join (by decide) sg166 sg11651

lemma sg19494 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11676

lemma sg19495 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14305

lemma sg19496 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11678

lemma sg19497 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11679

lemma sg19498 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11656

lemma sg19499 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,4,4,4,2] := by
  exact rowSquare_join (by decide) sg165 sg11680

lemma sg19500 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11657

lemma sg19501 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11681

lemma sg19502 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,3,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11682

lemma sg19503 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11659

lemma sg19504 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11683

lemma sg19505 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11660

lemma sg19506 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11684

lemma sg19507 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,4,4,1] := by
  exact rowSquare_join (by decide) sg165 sg11685

lemma sg19508 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg12907

lemma sg19509 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11663

lemma sg19510 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,2,2] := by
  exact rowSquare_join (by decide) sg165 sg11686

lemma sg19511 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11687

lemma sg19512 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,5,5,4] := by
  exact rowSquare_join (by decide) sg166 sg11665

lemma sg19513 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11657

lemma sg19514 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,3,2,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11688

lemma sg19515 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11666

lemma sg19516 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,3,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11689

lemma sg19517 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11659

lemma sg19518 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11668

lemma sg19519 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,2,2] := by
  exact rowSquare_join (by decide) sg165 sg11690

lemma sg19520 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,3,1] := by
  exact rowSquare_join (by decide) sg165 sg11691

lemma sg19521 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,4,4] := by
  exact rowSquare_join (by decide) sg166 sg11670

lemma sg19522 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,5,1,1,1] := by
  exact rowSquare_join (by decide) sg167 sg11663

lemma sg19523 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,5,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11692

lemma sg19524 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,5,3] := by
  exact rowSquare_join (by decide) sg364 sg11094

lemma sg19525 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,6,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11693

lemma sg19526 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,8,6,6,2] := by
  exact rowSquare_join (by decide) sg364 sg11095

lemma sg19527 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg14 sg14294

lemma sg19528 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11675

lemma sg19529 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg166 sg11676

lemma sg19530 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,3,3,3] := by
  exact rowSquare_join (by decide) sg14 sg14296

lemma sg19531 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11677

lemma sg19532 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14306

lemma sg19533 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg166 sg11678

lemma sg19534 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,3,2] := by
  exact rowSquare_join (by decide) sg166 sg11679

lemma sg19535 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,9,4,4,4,1] := by
  exact rowSquare_join (by decide) sg166 sg11680

lemma sg19536 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,3,3,3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg3551 sg4167

lemma sg19537 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,3,3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg3550 sg4168

lemma sg19538 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg165 sg11694

lemma sg19539 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15144

lemma sg19540 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,2,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12533

lemma sg19541 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11695

lemma sg19542 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg15145

lemma sg19543 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg15146

lemma sg19544 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15147

lemma sg19545 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15148

lemma sg19546 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,4,4,4,1] := by
  exact rowSquare_join (by decide) sg3537 sg4184

lemma sg19547 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg165 sg11696

lemma sg19548 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,3,3,3,3,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15149

lemma sg19549 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg166 sg11694

lemma sg19550 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg165 sg11697

lemma sg19551 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,3,3,3,3] := by
  exact rowSquare_join (by decide) sg1 sg15150

lemma sg19552 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,2,2,2,2] := by
  exact rowSquare_join (by decide) sg84 sg12534

lemma sg19553 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg166 sg11695

lemma sg19554 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,3,3,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11698

lemma sg19555 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg165 sg11699

lemma sg19556 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,2,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11700

lemma sg19557 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,2,2] := by
  exact rowSquare_join (by decide) sg3 sg14733

lemma sg19558 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15151

lemma sg19559 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,4,4,4,4] := by
  exact rowSquare_join (by decide) sg697 sg11058

lemma sg19560 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg167 sg11694

lemma sg19561 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg168 sg11625

lemma sg19562 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11701

lemma sg19563 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,3,3,3,2] := by
  exact rowSquare_join (by decide) sg489 sg8909

lemma sg19564 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg167 sg11695

lemma sg19565 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11702

lemma sg19566 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,4,3,2,2] := by
  exact rowSquare_join (by decide) sg490 sg8909

lemma sg19567 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,4,3,3,1] := by
  exact rowSquare_join (by decide) sg489 sg8910

lemma sg19568 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg168 sg11627

lemma sg19569 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,5,5,5,2,2,1,1] := by
  exact rowSquare_join (by decide) sg165 sg11703

lemma sg19570 : RowSquare [7,7,3,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg101 sg12673

lemma sg19571 : RowSquare [7,7,3,2,2,2,2,2,2,1,1] [6,4,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg101 sg12674

lemma sg19572 : RowSquare [7,7,3,2,2,2,2,2,2,1,1] [6,5,2,2,2,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg202 sg11799

lemma sg19573 : RowSquare [7,7,3,2,2,2,2,2,2,1,1] [7,3,2,2,2,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg102 sg12674

lemma sg19574 : RowSquare [7,7,3,2,2,2,2,2,2,1,1] [8,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg103 sg12669

lemma sg19575 : RowSquare [7,7,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3311 sg4167

lemma sg19576 : RowSquare [7,7,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1748 sg6469

lemma sg19577 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg3578 sg4158

lemma sg19578 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg3309 sg4466

lemma sg19579 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,5,5] := by
  exact rowSquare_join (by decide) sg3309 sg4468

lemma sg19580 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14314

lemma sg19581 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg3468 sg4350

lemma sg19582 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3462 sg4351

lemma sg19583 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3469 sg4350

lemma sg19584 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3463 sg4351

lemma sg19585 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3672 sg4051

lemma sg19586 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3464 sg4351

lemma sg19587 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,3] := by
  exact rowSquare_join (by decide) sg3275 sg4517

lemma sg19588 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3676 sg4051

lemma sg19589 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3465 sg4351

lemma sg19590 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,3] := by
  exact rowSquare_join (by decide) sg3275 sg4518

lemma sg19591 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3466 sg4351

lemma sg19592 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,5,5,5,1,1] := by
  exact rowSquare_join (by decide) sg3581 sg4158

lemma sg19593 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg401 sg11550

lemma sg19594 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg3675 sg4053

lemma sg19595 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,6,6,6,5] := by
  exact rowSquare_join (by decide) sg3309 sg4471

lemma sg19596 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3467 sg4351

lemma sg19597 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,3,2] := by
  exact rowSquare_join (by decide) sg3277 sg4518

lemma sg19598 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg402 sg11550

lemma sg19599 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg3578 sg4159

lemma sg19600 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,5,5,5,1] := by
  exact rowSquare_join (by decide) sg3679 sg4053

lemma sg19601 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg401 sg11552

lemma sg19602 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,7,6,5,5] := by
  exact rowSquare_join (by decide) sg3309 sg4472

lemma sg19603 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg407 sg11549

lemma sg19604 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg707 sg11056

lemma sg19605 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14315

lemma sg19606 : RowSquare [8,6,2,2,2,2,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg402 sg11551

lemma sg19607 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,6,6,1] := by
  exact rowSquare_join (by decide) sg3309 sg4438

lemma sg19608 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,6] := by
  exact rowSquare_join (by decide) sg3556 sg4158

lemma sg19609 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14317

lemma sg19610 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,7,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14318

lemma sg19611 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,4] := by
  exact rowSquare_join (by decide) sg391 sg11550

lemma sg19612 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,4] := by
  exact rowSquare_join (by decide) sg391 sg11552

lemma sg19613 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,4] := by
  exact rowSquare_join (by decide) sg193 sg12340

lemma sg19614 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,4,3] := by
  exact rowSquare_join (by decide) sg14 sg14316

lemma sg19615 : RowSquare [8,6,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,5,5,4,4,4] := by
  exact rowSquare_join (by decide) sg697 sg11057

lemma sg19616 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2134 sg5739

lemma sg19617 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg15608

lemma sg19618 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2134 sg5740

lemma sg19619 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg2134 sg5741

lemma sg19620 : RowSquare [8,6,3,3,2,2,1,1,1,1,1,1,1] [4,4,4,4,3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14319

lemma sg19621 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg15616

lemma sg19622 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,3,3,3,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg888 sg8892

lemma sg19623 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg8891

lemma sg19624 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,4,3,3,3,3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg889 sg8892

lemma sg19625 : RowSquare [8,6,4,3,2,1,1,1,1,1,1,1,1] [4,4,4,4,4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg12916

lemma sg19626 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [6,6,6,4,4,3,1,1] := by
  exact rowSquare_join (by decide) sg2708 sg4890

lemma sg19627 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3384 sg4351

lemma sg19628 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,5,5,5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3533 sg4158

lemma sg19629 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,5,5,1,1] := by
  exact rowSquare_join (by decide) sg3309 sg4423

lemma sg19630 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,3,3] := by
  exact rowSquare_join (by decide) sg39 sg13504

lemma sg19631 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14321

lemma sg19632 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,4,2] := by
  exact rowSquare_join (by decide) sg39 sg13505

lemma sg19633 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,6,6,6,5,1] := by
  exact rowSquare_join (by decide) sg39 sg13506

lemma sg19634 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14323

lemma sg19635 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14324

lemma sg19636 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg3385 sg4354

lemma sg19637 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,3,3] := by
  exact rowSquare_join (by decide) sg40 sg13504

lemma sg19638 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14325

lemma sg19639 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,4,2] := by
  exact rowSquare_join (by decide) sg40 sg13505

lemma sg19640 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,6,5,5,1] := by
  exact rowSquare_join (by decide) sg40 sg13506

lemma sg19641 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14728

lemma sg19642 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3385 sg4355

lemma sg19643 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg14729

lemma sg19644 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14730

lemma sg19645 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,3,3,3,1] := by
  exact rowSquare_join (by decide) sg97 sg12720

lemma sg19646 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,3,3] := by
  exact rowSquare_join (by decide) sg97 sg12721

lemma sg19647 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14731

lemma sg19648 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,4,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14732

lemma sg19649 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14326

lemma sg19650 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,2,2,1] := by
  exact rowSquare_join (by decide) sg13 sg14327

lemma sg19651 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14328

lemma sg19652 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14329

lemma sg19653 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg14330

lemma sg19654 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14331

lemma sg19655 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14332

lemma sg19656 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14333

lemma sg19657 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [7,7,7,6,4] := by
  exact rowSquare_join (by decide) sg13 sg14334

lemma sg19658 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,3,3,3,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3661 sg4057

lemma sg19659 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3386 sg4351

lemma sg19660 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15159

lemma sg19661 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg0 sg15619

lemma sg19662 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg3663 sg4051

lemma sg19663 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,4,4,4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg0 sg15620

lemma sg19664 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,3,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg3387 sg4351

lemma sg19665 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15160

lemma sg19666 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12866

lemma sg19667 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg3307 sg4424

lemma sg19668 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,4,4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3388 sg4351

lemma sg19669 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12867

lemma sg19670 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3389 sg4351

lemma sg19671 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15161

lemma sg19672 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,4,4,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15162

lemma sg19673 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14336

lemma sg19674 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,3,3,2] := by
  exact rowSquare_join (by decide) sg1 sg15163

lemma sg19675 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15164

lemma sg19676 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15165

lemma sg19677 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1 sg15166

lemma sg19678 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,5,5,5,5,2,1] := by
  exact rowSquare_join (by decide) sg3537 sg4158

lemma sg19679 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,3,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1 sg15167

lemma sg19680 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12868

lemma sg19681 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3390 sg4351

lemma sg19682 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,4,4,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15168

lemma sg19683 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg40 sg12867

lemma sg19684 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3391 sg4351

lemma sg19685 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14338

lemma sg19686 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg15169

lemma sg19687 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12870

lemma sg19688 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,5,5,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12871

lemma sg19689 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg14734

lemma sg19690 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12536

lemma sg19691 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg12537

lemma sg19692 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12872

lemma sg19693 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,3,3] := by
  exact rowSquare_join (by decide) sg98 sg12721

lemma sg19694 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14735

lemma sg19695 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,5,5,1] := by
  exact rowSquare_join (by decide) sg3540 sg4158

lemma sg19696 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14343

lemma sg19697 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,4,1] := by
  exact rowSquare_join (by decide) sg13 sg14344

lemma sg19698 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,6,6,6,5] := by
  exact rowSquare_join (by decide) sg39 sg13507

lemma sg19699 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,3,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg39 sg12875

lemma sg19700 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg40 sg12868

lemma sg19701 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg3393 sg4351

lemma sg19702 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14345

lemma sg19703 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,4,4,4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3528 sg4295

lemma sg19704 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14320

lemma sg19705 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12878

lemma sg19706 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12880

lemma sg19707 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12881

lemma sg19708 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,3,3] := by
  exact rowSquare_join (by decide) sg39 sg13508

lemma sg19709 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,4,2] := by
  exact rowSquare_join (by decide) sg3308 sg4428

lemma sg19710 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,5,5,5,1] := by
  exact rowSquare_join (by decide) sg3309 sg4428

lemma sg19711 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12543

lemma sg19712 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg12544

lemma sg19713 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12882

lemma sg19714 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,4,3,3] := by
  exact rowSquare_join (by decide) sg227 sg12335

lemma sg19715 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,4,4,2] := by
  exact rowSquare_join (by decide) sg4 sg14737

lemma sg19716 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg12883

lemma sg19717 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,3,2] := by
  exact rowSquare_join (by decide) sg13 sg14351

lemma sg19718 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,4,1] := by
  exact rowSquare_join (by decide) sg13 sg14352

lemma sg19719 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,5,5] := by
  exact rowSquare_join (by decide) sg40 sg13507

lemma sg19720 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,2,2] := by
  exact rowSquare_join (by decide) sg13 sg14353

lemma sg19721 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,3,1] := by
  exact rowSquare_join (by decide) sg13 sg14354

lemma sg19722 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,6,6,4] := by
  exact rowSquare_join (by decide) sg13 sg14355

lemma sg19723 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,7,5,4] := by
  exact rowSquare_join (by decide) sg207 sg11609

lemma sg19724 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,7,6,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14357

lemma sg19725 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,7,6,2,1] := by
  exact rowSquare_join (by decide) sg39 sg12887

lemma sg19726 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,7,7,6,3] := by
  exact rowSquare_join (by decide) sg39 sg12888

lemma sg19727 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg4299

lemma sg19728 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg40 sg12875

lemma sg19729 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3523 sg4300

lemma sg19730 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14358

lemma sg19731 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg3530 sg4271

lemma sg19732 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg424 sg11544

lemma sg19733 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg12876

lemma sg19734 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg14322

lemma sg19735 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg228 sg12334

lemma sg19736 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14359

lemma sg19737 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg14360

lemma sg19738 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg2580 sg4991

lemma sg19739 : RowSquare [8,7,2,2,2,1,1,1,1,1,1,1,1,1,1] [8,8,5,5,5] := by
  exact rowSquare_join (by decide) sg17 sg14551

end UniversalTensorSquare
end
end

end OAI
