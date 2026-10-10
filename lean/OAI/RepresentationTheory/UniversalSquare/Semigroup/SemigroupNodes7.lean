import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes5

namespace OAI

/-! Semigroup Nodes 7. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3307 : RowSquare [6,3,1,1,1,1,1,1] [3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg889

lemma sg3308 : RowSquare [6,3,1,1,1,1,1,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg891

lemma sg3309 : RowSquare [6,3,1,1,1,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg892

lemma sg3310 : RowSquare [6,3,1,1,1,1,1,1] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg897

lemma sg3311 : RowSquare [6,3,2,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2626

lemma sg3312 : RowSquare [6,3,2,1,1,1,1] [3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2627

lemma sg3313 : RowSquare [6,3,2,1,1,1,1] [3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2632

lemma sg3314 : RowSquare [6,3,2,1,1,1,1] [3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2633

lemma sg3315 : RowSquare [6,3,2,1,1,1,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg807

lemma sg3316 : RowSquare [6,3,2,1,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg809

lemma sg3317 : RowSquare [6,3,2,1,1,1,1] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2589

lemma sg3318 : RowSquare [6,3,2,2,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg762

lemma sg3319 : RowSquare [6,3,2,2,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1629

lemma sg3320 : RowSquare [6,3,3,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg164 sg269

lemma sg3321 : RowSquare [6,3,3,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg163 sg269

lemma sg3322 : RowSquare [6,3,3,1,1,1] [2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg163 sg268

lemma sg3323 : RowSquare [6,3,3,1,1,1] [2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg163 sg267

lemma sg3324 : RowSquare [6,3,3,1,1,1] [2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg163 sg265

lemma sg3325 : RowSquare [6,3,3,1,1,1] [2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg92 sg442

lemma sg3326 : RowSquare [6,3,3,1,1,1] [3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg160 sg265

lemma sg3327 : RowSquare [6,3,3,1,1,1] [3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg441

lemma sg3328 : RowSquare [6,3,3,1,1,1] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg159 sg267

lemma sg3329 : RowSquare [6,3,3,1,1,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg89 sg442

lemma sg3330 : RowSquare [6,3,3,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg159 sg266

lemma sg3331 : RowSquare [6,3,3,1,1,1] [3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg159 sg264

lemma sg3332 : RowSquare [6,3,3,1,1,1] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg89 sg441

lemma sg3333 : RowSquare [6,3,3,1,1,1] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg159 sg262

lemma sg3334 : RowSquare [6,3,3,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg89 sg440

lemma sg3335 : RowSquare [6,3,3,1,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg161 sg263

lemma sg3336 : RowSquare [6,3,3,1,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg63 sg520

lemma sg3337 : RowSquare [6,3,3,2,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg759

lemma sg3338 : RowSquare [6,3,3,3] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg254

lemma sg3339 : RowSquare [6,3,3,3] [4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg66 sg480

lemma sg3340 : RowSquare [6,3,3,3] [4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg179 sg254

lemma sg3341 : RowSquare [6,3,3,3] [4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg66 sg481

lemma sg3342 : RowSquare [6,3,3,3] [4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg180 sg254

lemma sg3343 : RowSquare [6,3,3,3] [4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg68 sg481

lemma sg3344 : RowSquare [6,3,3,3] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg181 sg254

lemma sg3345 : RowSquare [6,3,3,3] [5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg182 sg254

lemma sg3346 : RowSquare [6,3,3,3] [5,4,3,3] := by
  exact rowSquare_join (by decide) sg183 sg254

lemma sg3347 : RowSquare [6,4,1,1,1,1,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1632

lemma sg3348 : RowSquare [6,4,1,1,1,1,1] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg13 sg1191

lemma sg3349 : RowSquare [6,4,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8 sg1327

lemma sg3350 : RowSquare [6,4,1,1,1,1,1] [5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1637

lemma sg3351 : RowSquare [6,4,1,1,1,1,1] [5,5,5] := by
  exact rowSquare_join (by decide) sg4 sg1641

lemma sg3352 : RowSquare [6,4,2,1,1,1] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1196

lemma sg3353 : RowSquare [6,4,2,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg762

lemma sg3354 : RowSquare [6,4,2,1,1,1] [5,5,5] := by
  exact rowSquare_join (by decide) sg97 sg440

lemma sg3355 : RowSquare [6,4,2,2,1] [3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2602

lemma sg3356 : RowSquare [6,4,2,2,1] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg4 sg1616

lemma sg3357 : RowSquare [6,4,3,1,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg790

lemma sg3358 : RowSquare [6,4,3,1,1] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg475

lemma sg3359 : RowSquare [6,4,3,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg792

lemma sg3360 : RowSquare [6,4,3,2] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg480

lemma sg3361 : RowSquare [6,4,3,2] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg481

lemma sg3362 : RowSquare [6,4,3,2] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg796

lemma sg3363 : RowSquare [6,4,3,2] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2110

lemma sg3364 : RowSquare [6,4,3,2] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg142 sg285

lemma sg3365 : RowSquare [6,4,3,2] [4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg123 sg331

lemma sg3366 : RowSquare [6,4,3,2] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg143 sg285

lemma sg3367 : RowSquare [6,4,3,2] [4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg511

lemma sg3368 : RowSquare [6,4,3,2] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg195 sg254

lemma sg3369 : RowSquare [6,4,3,2] [5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg124 sg331

lemma sg3370 : RowSquare [6,4,3,2] [5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg125 sg331

lemma sg3371 : RowSquare [6,4,3,2] [5,4,4,2] := by
  exact rowSquare_join (by decide) sg144 sg290

lemma sg3372 : RowSquare [6,4,3,2] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg511

lemma sg3373 : RowSquare [6,4,3,2] [6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg127 sg331

lemma sg3374 : RowSquare [6,4,3,2] [6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg128 sg331

lemma sg3375 : RowSquare [7,2,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2702

lemma sg3376 : RowSquare [7,2,1,1,1,1,1,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2707

lemma sg3377 : RowSquare [7,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2708

lemma sg3378 : RowSquare [7,2,1,1,1,1,1,1] [4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg2710

lemma sg3379 : RowSquare [7,2,1,1,1,1,1,1] [4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg2620

lemma sg3380 : RowSquare [7,2,1,1,1,1,1,1] [5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg2621

lemma sg3381 : RowSquare [7,3,1,1,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1663

lemma sg3382 : RowSquare [7,3,1,1,1,1,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1240

lemma sg3383 : RowSquare [7,3,1,1,1,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1664

lemma sg3384 : RowSquare [7,3,1,1,1,1,1] [4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1243

lemma sg3385 : RowSquare [7,3,1,1,1,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1667

lemma sg3386 : RowSquare [7,3,1,1,1,1,1] [5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1668

lemma sg3387 : RowSquare [7,3,1,1,1,1,1] [5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1240

lemma sg3388 : RowSquare [7,3,1,1,1,1,1] [5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg2 sg2123

lemma sg3389 : RowSquare [7,3,1,1,1,1,1] [5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1247

lemma sg3390 : RowSquare [7,3,1,1,1,1,1] [5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1249

lemma sg3391 : RowSquare [7,3,1,1,1,1,1] [5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1189

lemma sg3392 : RowSquare [7,3,1,1,1,1,1] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1188

lemma sg3393 : RowSquare [7,3,1,1,1,1,1] [5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1189

lemma sg3394 : RowSquare [7,3,1,1,1,1,1] [6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg1668

lemma sg3395 : RowSquare [7,3,1,1,1,1,1] [6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg7 sg1634

lemma sg3396 : RowSquare [7,3,1,1,1,1,1] [6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1193

lemma sg3397 : RowSquare [7,3,1,1,1,1,1] [6,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg800

lemma sg3398 : RowSquare [7,3,1,1,1,1,1] [6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1194

lemma sg3399 : RowSquare [7,3,1,1,1,1,1] [7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg1240

lemma sg3400 : RowSquare [7,3,1,1,1,1,1] [7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg1192

lemma sg3401 : RowSquare [7,3,2,1,1,1] [3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2630

lemma sg3402 : RowSquare [7,3,2,1,1,1] [3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2632

lemma sg3403 : RowSquare [7,3,2,1,1,1] [3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2633

lemma sg3404 : RowSquare [7,3,2,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg809

lemma sg3405 : RowSquare [7,3,2,1,1,1] [4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg517

lemma sg3406 : RowSquare [7,3,2,1,1,1] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg518

lemma sg3407 : RowSquare [7,3,2,1,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1673

lemma sg3408 : RowSquare [7,3,2,2,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg55 sg586

lemma sg3409 : RowSquare [7,3,3,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg62 sg586

lemma sg3410 : RowSquare [7,3,3,1,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg828

lemma sg3411 : RowSquare [7,3,3,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg829

lemma sg3412 : RowSquare [7,3,3,1,1] [4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg154 sg312

lemma sg3413 : RowSquare [7,3,3,1,1] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg154 sg313

lemma sg3414 : RowSquare [7,3,3,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg475

lemma sg3415 : RowSquare [7,3,3,1,1] [5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg157 sg312

lemma sg3416 : RowSquare [7,3,3,1,1] [5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg154 sg316

lemma sg3417 : RowSquare [7,3,3,2] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg286

lemma sg3418 : RowSquare [7,3,3,2] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg287

lemma sg3419 : RowSquare [7,3,3,2] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg833

lemma sg3420 : RowSquare [7,3,3,2] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg834

lemma sg3421 : RowSquare [7,3,3,2] [4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg548

lemma sg3422 : RowSquare [7,3,3,2] [4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg548

lemma sg3423 : RowSquare [7,3,3,2] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg285

lemma sg3424 : RowSquare [7,3,3,2] [4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg548

lemma sg3425 : RowSquare [7,3,3,2] [4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg286

lemma sg3426 : RowSquare [7,3,3,2] [4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg179 sg287

lemma sg3427 : RowSquare [7,3,3,2] [4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg87 sg481

lemma sg3428 : RowSquare [7,3,3,2] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg180 sg285

lemma sg3429 : RowSquare [7,3,3,2] [4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg181 sg285

lemma sg3430 : RowSquare [7,3,3,2] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg180 sg286

lemma sg3431 : RowSquare [7,3,3,2] [4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg180 sg287

lemma sg3432 : RowSquare [7,3,3,2] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg480

lemma sg3433 : RowSquare [7,3,3,2] [4,4,4,2,1] := by
  exact rowSquare_join (by decide) sg181 sg286

lemma sg3434 : RowSquare [7,3,3,2] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg181 sg287

lemma sg3435 : RowSquare [7,3,3,2] [5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg548

lemma sg3436 : RowSquare [7,3,3,2] [5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg288

lemma sg3437 : RowSquare [7,3,3,2] [5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg70 sg548

lemma sg3438 : RowSquare [7,3,3,2] [5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg289

lemma sg3439 : RowSquare [7,3,3,2] [5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg290

lemma sg3440 : RowSquare [7,3,3,2] [5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg182 sg286

lemma sg3441 : RowSquare [7,3,3,2] [5,3,3,3,1] := by
  exact rowSquare_join (by decide) sg218 sg254

lemma sg3442 : RowSquare [7,3,3,2] [5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg548

lemma sg3443 : RowSquare [7,3,3,2] [5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg291

lemma sg3444 : RowSquare [7,3,3,2] [5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg180 sg289

lemma sg3445 : RowSquare [7,3,3,2] [5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg292

lemma sg3446 : RowSquare [7,3,3,2] [5,4,3,2,1] := by
  exact rowSquare_join (by decide) sg180 sg290

lemma sg3447 : RowSquare [7,3,3,2] [5,4,3,3] := by
  exact rowSquare_join (by decide) sg219 sg254

lemma sg3448 : RowSquare [7,3,3,2] [5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg184 sg286

lemma sg3449 : RowSquare [7,3,3,2] [5,4,4,2] := by
  exact rowSquare_join (by decide) sg181 sg290

lemma sg3450 : RowSquare [7,3,3,2] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg294

lemma sg3451 : RowSquare [7,3,3,2] [5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg185 sg285

lemma sg3452 : RowSquare [7,3,3,2] [5,5,2,2,1] := by
  exact rowSquare_join (by decide) sg180 sg291

lemma sg3453 : RowSquare [7,3,3,2] [5,5,3,1,1] := by
  exact rowSquare_join (by decide) sg180 sg292

lemma sg3454 : RowSquare [7,3,3,2] [5,5,3,2] := by
  exact rowSquare_join (by decide) sg181 sg291

lemma sg3455 : RowSquare [7,3,3,2] [5,5,4,1] := by
  exact rowSquare_join (by decide) sg181 sg292

lemma sg3456 : RowSquare [7,4,1,1,1,1] [4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1259

lemma sg3457 : RowSquare [7,4,1,1,1,1] [4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg808

lemma sg3458 : RowSquare [7,4,1,1,1,1] [4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg39 sg809

lemma sg3459 : RowSquare [7,4,1,1,1,1] [4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg807

lemma sg3460 : RowSquare [7,4,1,1,1,1] [4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg808

lemma sg3461 : RowSquare [7,4,1,1,1,1] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg40 sg809

lemma sg3462 : RowSquare [7,4,1,1,1,1] [5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1678

lemma sg3463 : RowSquare [7,4,1,1,1,1] [5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1258

lemma sg3464 : RowSquare [7,4,1,1,1,1] [5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg812

lemma sg3465 : RowSquare [7,4,1,1,1,1] [5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg814

lemma sg3466 : RowSquare [7,4,1,1,1,1] [5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg518

lemma sg3467 : RowSquare [7,4,1,1,1,1] [5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg814

lemma sg3468 : RowSquare [7,4,1,1,1,1] [6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5 sg1678

lemma sg3469 : RowSquare [7,4,1,1,1,1] [6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg517

lemma sg3470 : RowSquare [7,4,2,1,1] [3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg534

lemma sg3471 : RowSquare [7,4,2,1,1] [3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg838

lemma sg3472 : RowSquare [7,4,2,1,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg535

lemma sg3473 : RowSquare [7,4,2,1,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg839

lemma sg3474 : RowSquare [7,4,2,1,1] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg536

lemma sg3475 : RowSquare [7,4,2,1,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg537

lemma sg3476 : RowSquare [7,4,2,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg841

lemma sg3477 : RowSquare [7,4,2,1,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg911

lemma sg3478 : RowSquare [7,4,2,1,1] [4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg165 sg312

lemma sg3479 : RowSquare [7,4,2,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg911

lemma sg3480 : RowSquare [7,4,2,1,1] [4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg166 sg312

lemma sg3481 : RowSquare [7,4,2,1,1] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg165 sg313

lemma sg3482 : RowSquare [7,4,2,1,1] [4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg270

lemma sg3483 : RowSquare [7,4,2,1,1] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg166 sg313

lemma sg3484 : RowSquare [7,4,2,1,1] [4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg77 sg535

lemma sg3485 : RowSquare [7,4,2,1,1] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg194 sg270

lemma sg3486 : RowSquare [7,4,2,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg543

lemma sg3487 : RowSquare [7,4,2,1,1] [5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg28 sg911

lemma sg3488 : RowSquare [7,4,2,1,1] [5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg168 sg312

lemma sg3489 : RowSquare [7,4,2,1,1] [5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg193 sg272

lemma sg3490 : RowSquare [7,4,2,1,1] [5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg29 sg911

lemma sg3491 : RowSquare [7,4,2,1,1] [5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg273

lemma sg3492 : RowSquare [7,4,2,1,1] [5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg170 sg312

lemma sg3493 : RowSquare [7,4,2,1,1] [5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg196 sg270

lemma sg3494 : RowSquare [7,4,2,1,1] [5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg276

lemma sg3495 : RowSquare [7,4,2,1,1] [5,4,4,1,1] := by
  exact rowSquare_join (by decide) sg198 sg270

lemma sg3496 : RowSquare [7,4,2,1,1] [6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg30 sg911

lemma sg3497 : RowSquare [7,4,2,1,1] [6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg277

lemma sg3498 : RowSquare [7,4,2,1,1] [6,3,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg277

lemma sg3499 : RowSquare [7,4,2,1,1] [6,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg279

lemma sg3500 : RowSquare [7,4,2,2] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg297

lemma sg3501 : RowSquare [7,4,3,1] [2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg306

lemma sg3502 : RowSquare [7,4,3,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg850

lemma sg3503 : RowSquare [7,4,3,1] [3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1232

lemma sg3504 : RowSquare [7,4,3,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg308

lemma sg3505 : RowSquare [7,4,3,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg854

lemma sg3506 : RowSquare [7,4,3,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg850

lemma sg3507 : RowSquare [7,4,3,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg850

lemma sg3508 : RowSquare [7,4,3,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1233

lemma sg3509 : RowSquare [7,4,3,1] [5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg798

lemma sg3510 : RowSquare [7,4,3,1] [5,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg193 sg288

lemma sg3511 : RowSquare [7,4,3,1] [5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg798

lemma sg3512 : RowSquare [7,4,4] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg516

lemma sg3513 : RowSquare [7,5,2,1] [3,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg849

lemma sg3514 : RowSquare [7,5,2,1] [3,3,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg849

lemma sg3515 : RowSquare [7,5,2,1] [3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg167 sg330

lemma sg3516 : RowSquare [7,5,2,1] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg563

lemma sg3517 : RowSquare [7,5,2,1] [4,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg41 sg849

lemma sg3518 : RowSquare [7,5,2,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg850

lemma sg3519 : RowSquare [7,5,2,1] [4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg170 sg330

lemma sg3520 : RowSquare [7,6,2] [3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg207 sg306

lemma sg3522 : RowSquare [8,1,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg430

lemma sg3523 : RowSquare [8,1,1,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg429

lemma sg3524 : RowSquare [8,1,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg733

lemma sg3525 : RowSquare [8,1,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg1662

lemma sg3526 : RowSquare [8,1,1,1,1,1,1,1] [3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2699

lemma sg3527 : RowSquare [8,1,1,1,1,1,1,1] [3,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg49 sg732

lemma sg3528 : RowSquare [8,1,1,1,1,1,1,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2155

lemma sg3529 : RowSquare [8,1,1,1,1,1,1,1] [4,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2700

lemma sg3530 : RowSquare [8,1,1,1,1,1,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg1182

lemma sg3531 : RowSquare [8,1,1,1,1,1,1,1] [5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2154

lemma sg3532 : RowSquare [8,1,1,1,1,1,1,1] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg1659

lemma sg3533 : RowSquare [8,2,1,1,1,1,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2707

lemma sg3534 : RowSquare [8,2,1,1,1,1,1] [3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2708

lemma sg3535 : RowSquare [8,2,1,1,1,1,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2255

lemma sg3536 : RowSquare [8,2,1,1,1,1,1] [4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg2256

lemma sg3537 : RowSquare [8,2,1,1,1,1,1] [4,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg2710

lemma sg3538 : RowSquare [8,2,1,1,1,1,1] [4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2711

lemma sg3539 : RowSquare [8,2,1,1,1,1,1] [4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2712

lemma sg3540 : RowSquare [8,2,1,1,1,1,1] [4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg1750

lemma sg3541 : RowSquare [8,2,1,1,1,1,1] [5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1240

lemma sg3542 : RowSquare [8,2,1,1,1,1,1] [5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2157

lemma sg3543 : RowSquare [8,2,1,1,1,1,1] [5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1240

lemma sg3544 : RowSquare [8,2,1,1,1,1,1] [5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1241

lemma sg3545 : RowSquare [8,2,1,1,1,1,1] [5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg1750

lemma sg3546 : RowSquare [8,2,1,1,1,1,1] [5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1241

lemma sg3547 : RowSquare [8,2,1,1,1,1,1] [6,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg1240

lemma sg3548 : RowSquare [8,2,1,1,1,1,1] [6,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1245

lemma sg3549 : RowSquare [8,2,1,1,1,1,1] [6,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1245

lemma sg3550 : RowSquare [8,2,1,1,1,1,1] [7,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg1245

lemma sg3551 : RowSquare [8,2,1,1,1,1,1] [8,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg1192

lemma sg3552 : RowSquare [8,2,2,1,1,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg888

lemma sg3553 : RowSquare [8,2,2,1,1,1] [3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg889

lemma sg3554 : RowSquare [8,2,2,1,1,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg890

lemma sg3555 : RowSquare [8,2,2,1,1,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg891

lemma sg3556 : RowSquare [8,2,2,1,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg892

lemma sg3557 : RowSquare [8,2,2,1,1,1] [4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg894

lemma sg3558 : RowSquare [8,2,2,1,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg1329

lemma sg3559 : RowSquare [8,2,2,2,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg586

lemma sg3560 : RowSquare [8,2,2,2,1] [3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg312

lemma sg3561 : RowSquare [8,2,2,2,1] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg586

lemma sg3562 : RowSquare [8,2,2,2,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg313

lemma sg3563 : RowSquare [8,2,2,2,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg586

lemma sg3564 : RowSquare [8,2,2,2,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg314

lemma sg3565 : RowSquare [8,2,2,2,1] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg315

lemma sg3566 : RowSquare [8,2,2,2,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg70 sg586

lemma sg3567 : RowSquare [8,2,2,2,1] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg313

lemma sg3568 : RowSquare [8,2,2,2,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg586

lemma sg3569 : RowSquare [8,2,2,2,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg589

lemma sg3570 : RowSquare [8,2,2,2,1] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg181 sg315

lemma sg3571 : RowSquare [8,3,1,1,1,1] [2,2,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1327

lemma sg3572 : RowSquare [8,3,1,1,1,1] [3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1327

lemma sg3573 : RowSquare [8,3,1,1,1,1] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1329

lemma sg3574 : RowSquare [8,3,1,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1756

lemma sg3575 : RowSquare [8,3,1,1,1,1] [3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1330

lemma sg3576 : RowSquare [8,3,1,1,1,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1758

lemma sg3577 : RowSquare [8,3,1,1,1,1] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1331

lemma sg3578 : RowSquare [8,3,1,1,1,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg1332

lemma sg3579 : RowSquare [8,3,1,1,1,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg888

lemma sg3580 : RowSquare [8,3,1,1,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg888

lemma sg3581 : RowSquare [8,3,1,1,1,1] [4,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg5 sg1758

lemma sg3582 : RowSquare [8,3,1,1,1,1] [4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1760

lemma sg3583 : RowSquare [8,3,1,1,1,1] [4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg890

lemma sg3584 : RowSquare [8,3,1,1,1,1] [4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg1762

lemma sg3585 : RowSquare [8,3,1,1,1,1] [4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg39 sg891

lemma sg3586 : RowSquare [8,3,1,1,1,1] [4,3,3,3,2] := by
  exact rowSquare_join (by decide) sg39 sg892

lemma sg3587 : RowSquare [8,3,1,1,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1329

lemma sg3588 : RowSquare [8,3,1,1,1,1] [4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg1338

lemma sg3589 : RowSquare [8,3,1,1,1,1] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg14 sg1332

lemma sg3590 : RowSquare [8,3,1,1,1,1] [4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg890

lemma sg3591 : RowSquare [8,3,1,1,1,1] [4,4,3,2,1,1] := by
  exact rowSquare_join (by decide) sg40 sg891

lemma sg3592 : RowSquare [8,3,1,1,1,1] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg40 sg892

lemma sg3593 : RowSquare [8,3,1,1,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1766

lemma sg3594 : RowSquare [8,3,1,1,1,1] [5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg893

lemma sg3595 : RowSquare [8,3,1,1,1,1] [5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg6 sg1758

lemma sg3596 : RowSquare [8,3,1,1,1,1] [5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg888

lemma sg3597 : RowSquare [8,3,1,1,1,1] [5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg893

lemma sg3598 : RowSquare [8,3,1,1,1,1] [5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg894

lemma sg3599 : RowSquare [8,3,1,1,1,1] [5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg1762

lemma sg3600 : RowSquare [8,3,1,1,1,1] [5,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg517

lemma sg3601 : RowSquare [8,3,1,1,1,1] [5,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg895

lemma sg3602 : RowSquare [8,3,1,1,1,1] [5,3,3,2,2] := by
  exact rowSquare_join (by decide) sg45 sg809

lemma sg3603 : RowSquare [8,3,1,1,1,1] [5,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg42 sg889

lemma sg3604 : RowSquare [8,3,1,1,1,1] [5,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg894

lemma sg3605 : RowSquare [8,3,1,1,1,1] [5,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg39 sg897

lemma sg3606 : RowSquare [8,3,1,1,1,1] [5,4,2,2,2] := by
  exact rowSquare_join (by decide) sg46 sg809

lemma sg3607 : RowSquare [8,3,1,1,1,1] [5,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg518

lemma sg3608 : RowSquare [8,3,1,1,1,1] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg1338

lemma sg3609 : RowSquare [8,3,1,1,1,1] [5,5,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg897

lemma sg3610 : RowSquare [8,3,1,1,1,1] [6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg15 sg1332

lemma sg3611 : RowSquare [8,3,1,1,1,1] [6,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg811

lemma sg3612 : RowSquare [8,3,1,1,1,1] [6,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg814

lemma sg3613 : RowSquare [8,3,2,1,1] [2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg910

lemma sg3614 : RowSquare [8,3,2,1,1] [2,2,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg586

lemma sg3615 : RowSquare [8,3,2,1,1] [3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg587

lemma sg3616 : RowSquare [8,3,2,1,1] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg76 sg586

lemma sg3617 : RowSquare [8,3,2,1,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg588

lemma sg3618 : RowSquare [8,3,2,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg77 sg586

lemma sg3619 : RowSquare [8,3,2,1,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg913

lemma sg3620 : RowSquare [8,3,2,1,1] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg589

lemma sg3621 : RowSquare [8,3,2,1,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg74 sg590

lemma sg3622 : RowSquare [8,3,2,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg915

lemma sg3623 : RowSquare [8,3,2,1,1] [4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg534

lemma sg3624 : RowSquare [8,3,2,1,1] [4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg534

lemma sg3625 : RowSquare [8,3,2,1,1] [4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg314

lemma sg3626 : RowSquare [8,3,2,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg586

lemma sg3627 : RowSquare [8,3,2,1,1] [4,4,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg535

lemma sg3628 : RowSquare [8,3,2,1,1] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg194 sg314

lemma sg3629 : RowSquare [8,3,2,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg536

lemma sg3630 : RowSquare [8,3,2,1,1] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg195 sg315

lemma sg3631 : RowSquare [8,3,2,1,1] [5,5,5] := by
  exact rowSquare_join (by decide) sg89 sg543

lemma sg3632 : RowSquare [8,3,2,2] [2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg330

lemma sg3633 : RowSquare [8,3,2,2] [3,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg330

lemma sg3634 : RowSquare [8,3,2,2] [3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg331

lemma sg3635 : RowSquare [8,3,2,2] [3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg330

lemma sg3636 : RowSquare [8,3,2,2] [3,3,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg181 sg330

lemma sg3637 : RowSquare [8,3,2,2] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg334

lemma sg3638 : RowSquare [8,3,2,2] [4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg182 sg330

lemma sg3639 : RowSquare [8,3,2,2] [4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg183 sg330

lemma sg3640 : RowSquare [8,3,2,2] [4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg184 sg330

lemma sg3641 : RowSquare [8,3,2,2] [4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg185 sg330

lemma sg3642 : RowSquare [8,3,2,2] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg180 sg332

lemma sg3643 : RowSquare [8,3,2,2] [4,4,3,2,2] := by
  exact rowSquare_join (by decide) sg180 sg333

lemma sg3644 : RowSquare [8,3,2,2] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg615

lemma sg3645 : RowSquare [8,3,2,2] [4,4,4,3] := by
  exact rowSquare_join (by decide) sg181 sg334

lemma sg3646 : RowSquare [8,3,2,2] [5,5,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg342

lemma sg3647 : RowSquare [8,3,3,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg348

lemma sg3648 : RowSquare [8,3,3,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg943

lemma sg3649 : RowSquare [8,3,3,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg550

lemma sg3650 : RowSquare [8,4,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg586

lemma sg3651 : RowSquare [8,4,1,1,1] [4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg534

lemma sg3652 : RowSquare [8,4,1,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg97 sg536

lemma sg3653 : RowSquare [8,4,2,1] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg356

lemma sg3654 : RowSquare [8,4,2,1] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg358

lemma sg3655 : RowSquare [8,4,2,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg961

lemma sg3656 : RowSquare [8,4,3] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg975

lemma sg3657 : RowSquare [8,4,3] [3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg636

lemma sg3658 : RowSquare [8,4,3] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg977

lemma sg3659 : RowSquare [8,4,3] [4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg975

lemma sg3660 : RowSquare [8,4,3] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg641

lemma sg3661 : RowSquare [9,1,1,1,1,1,1] [3,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2251

lemma sg3662 : RowSquare [9,1,1,1,1,1,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2255

lemma sg3663 : RowSquare [9,1,1,1,1,1,1] [4,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2256

lemma sg3664 : RowSquare [9,1,1,1,1,1,1] [5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2258

lemma sg3665 : RowSquare [9,1,1,1,1,1,1] [5,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2259

lemma sg3666 : RowSquare [9,1,1,1,1,1,1] [5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2260

lemma sg3667 : RowSquare [9,1,1,1,1,1,1] [5,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2261

lemma sg3668 : RowSquare [9,1,1,1,1,1,1] [5,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2262

lemma sg3669 : RowSquare [9,1,1,1,1,1,1] [5,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg2263

lemma sg3670 : RowSquare [9,1,1,1,1,1,1] [7,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg1240

lemma sg3671 : RowSquare [9,2,1,1,1,1] [3,3,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1327

lemma sg3672 : RowSquare [9,2,1,1,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1329

lemma sg3673 : RowSquare [9,2,1,1,1,1] [4,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1330

lemma sg3674 : RowSquare [9,2,1,1,1,1] [4,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg1331

lemma sg3675 : RowSquare [9,2,1,1,1,1] [4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg16 sg1332

lemma sg3676 : RowSquare [9,2,1,1,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1329

lemma sg3677 : RowSquare [9,2,1,1,1,1] [4,4,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1330

lemma sg3678 : RowSquare [9,2,1,1,1,1] [4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg1331

lemma sg3679 : RowSquare [9,2,1,1,1,1] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg17 sg1332

lemma sg3680 : RowSquare [9,2,1,1,1,1] [5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg7 sg1758

lemma sg3681 : RowSquare [9,2,1,1,1,1] [5,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg18 sg1332

lemma sg3682 : RowSquare [9,2,1,1,1,1] [6,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg1331

lemma sg3683 : RowSquare [9,2,1,1,1,1] [6,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg19 sg1332

lemma sg3684 : RowSquare [9,2,1,1,1,1] [6,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg894

lemma sg3685 : RowSquare [9,2,2,1,1] [3,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg87 sg586

lemma sg3686 : RowSquare [9,2,2,1,1] [3,3,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg586

lemma sg3687 : RowSquare [9,2,2,1,1] [3,3,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg998

lemma sg3688 : RowSquare [9,2,2,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg586

lemma sg3689 : RowSquare [9,2,2,1,1] [3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg999

lemma sg3690 : RowSquare [9,2,2,1,1] [3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg32 sg1000

lemma sg3691 : RowSquare [9,2,2,1,1] [3,3,3,3,3] := by
  exact rowSquare_join (by decide) sg32 sg1001

lemma sg3692 : RowSquare [9,2,2,1,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg90 sg586

lemma sg3693 : RowSquare [9,2,2,1,1] [4,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg91 sg586

lemma sg3694 : RowSquare [9,2,2,1,1] [4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg33 sg1000

lemma sg3695 : RowSquare [9,2,2,1,1] [4,4,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg586

lemma sg3696 : RowSquare [9,2,2,1,1] [4,4,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg588

lemma sg3697 : RowSquare [9,2,2,1,1] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg1006

lemma sg3698 : RowSquare [9,2,2,1,1] [4,4,3,3,1] := by
  exact rowSquare_join (by decide) sg88 sg590

lemma sg3699 : RowSquare [9,2,2,1,1] [4,4,4,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg589

lemma sg3700 : RowSquare [9,2,2,1,1] [5,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg93 sg586

lemma sg3701 : RowSquare [9,2,2,2] [3,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg370

lemma sg3702 : RowSquare [9,2,2,2] [3,3,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg371

lemma sg3703 : RowSquare [9,2,2,2] [3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg373

lemma sg3704 : RowSquare [9,2,2,2] [4,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg371

lemma sg3705 : RowSquare [9,2,2,2] [4,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg372

lemma sg3706 : RowSquare [9,2,2,2] [4,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg179 sg373

lemma sg3707 : RowSquare [9,2,2,2] [4,4,2,2,2,1] := by
  exact rowSquare_join (by decide) sg180 sg371

end UniversalTensorSquare
end
end

end OAI
