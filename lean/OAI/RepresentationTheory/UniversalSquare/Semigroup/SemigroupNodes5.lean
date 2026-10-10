import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Semigroup.SemigroupNodes4

namespace OAI

/-! Semigroup Nodes 5. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg2493 : RowSquare [3,2,2,2,1,1,1,1,1] [5,4,4,1] := by
  exact rowSquare_join (by decide) sg207 sg220

lemma sg2494 : RowSquare [3,2,2,2,1,1,1,1,1] [5,5,4] := by
  exact rowSquare_join (by decide) sg97 sg395

lemma sg2495 : RowSquare [3,3,1,1,1,1,1,1,1,1] [6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg218 sg218

lemma sg2496 : RowSquare [3,3,1,1,1,1,1,1,1,1] [6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg218 sg220

lemma sg2497 : RowSquare [3,3,1,1,1,1,1,1,1,1] [6,4,4] := by
  exact rowSquare_join (by decide) sg220 sg220

lemma sg2498 : RowSquare [3,3,1,1,1,1,1,1,1,1] [7,5,1,1] := by
  exact rowSquare_join (by decide) sg219 sg223

lemma sg2499 : RowSquare [3,3,2,1,1,1,1,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg390

lemma sg2500 : RowSquare [3,3,2,1,1,1,1,1,1] [5,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg193 sg219

lemma sg2501 : RowSquare [3,3,2,1,1,1,1,1,1] [5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg220

lemma sg2502 : RowSquare [3,3,2,1,1,1,1,1,1] [5,3,3,3] := by
  exact rowSquare_join (by decide) sg90 sg390

lemma sg2503 : RowSquare [3,3,2,1,1,1,1,1,1] [5,4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg636

lemma sg2504 : RowSquare [3,3,2,2,1,1,1,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg193 sg193

lemma sg2505 : RowSquare [3,3,3,2,1,1,1] [7,7] := by
  exact rowSquare_join (by decide) sg92 sg311

lemma sg2506 : RowSquare [3,3,3,2,1,1,1] [9,5] := by
  exact rowSquare_join (by decide) sg3 sg1130

lemma sg2507 : RowSquare [3,3,3,2,1,1,1] [11,3] := by
  exact rowSquare_join (by decide) sg128 sg109

lemma sg2508 : RowSquare [4,2,1,1,1,1,1,1,1,1] [6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg231

lemma sg2509 : RowSquare [4,2,1,1,1,1,1,1,1,1] [6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg232

lemma sg2510 : RowSquare [4,2,1,1,1,1,1,1,1,1] [6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg104 sg371

lemma sg2511 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg108 sg330

lemma sg2512 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg233

lemma sg2513 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg231

lemma sg2514 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,2,2,2,1] := by
  exact rowSquare_join (by decide) sg49 sg616

lemma sg2515 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg232

lemma sg2516 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,3,2,1,1] := by
  exact rowSquare_join (by decide) sg180 sg231

lemma sg2517 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,3,2,2] := by
  exact rowSquare_join (by decide) sg106 sg373

lemma sg2518 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,3,3,1] := by
  exact rowSquare_join (by decide) sg181 sg231

lemma sg2519 : RowSquare [4,2,1,1,1,1,1,1,1,1] [7,4,1,1,1] := by
  exact rowSquare_join (by decide) sg180 sg232

lemma sg2520 : RowSquare [4,2,2,1,1,1,1,1,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg227

lemma sg2521 : RowSquare [4,3,1,1,1,1,1,1,1] [6,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg940

lemma sg2522 : RowSquare [4,3,1,1,1,1,1,1,1] [6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg224

lemma sg2523 : RowSquare [4,3,1,1,1,1,1,1,1] [6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg225

lemma sg2524 : RowSquare [4,3,1,1,1,1,1,1,1] [7,7] := by
  exact rowSquare_join (by decide) sg92 sg383

lemma sg2525 : RowSquare [4,3,1,1,1,1,1,1,1] [8,6] := by
  exact rowSquare_join (by decide) sg0 sg2031

lemma sg2526 : RowSquare [4,3,1,1,1,1,1,1,1] [9,5] := by
  exact rowSquare_join (by decide) sg5 sg1122

lemma sg2527 : RowSquare [4,3,1,1,1,1,1,1,1] [10,4] := by
  exact rowSquare_join (by decide) sg14 sg719

lemma sg2528 : RowSquare [4,3,2,1,1,1,1,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg194

lemma sg2529 : RowSquare [4,3,2,1,1,1,1,1] [3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg371

lemma sg2530 : RowSquare [4,3,2,1,1,1,1,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg195

lemma sg2531 : RowSquare [4,3,2,1,1,1,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg616

lemma sg2532 : RowSquare [4,3,2,1,1,1,1,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg193 sg179

lemma sg2533 : RowSquare [4,3,2,1,1,1,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg180

lemma sg2534 : RowSquare [4,3,2,1,1,1,1,1] [5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20 sg849

lemma sg2535 : RowSquare [4,3,2,1,1,1,1,1] [7,7] := by
  exact rowSquare_join (by decide) sg92 sg342

lemma sg2536 : RowSquare [4,3,2,1,1,1,1,1] [8,6] := by
  exact rowSquare_join (by decide) sg10 sg722

lemma sg2537 : RowSquare [4,3,2,1,1,1,1,1] [9,5] := by
  exact rowSquare_join (by decide) sg10 sg724

lemma sg2538 : RowSquare [4,3,2,1,1,1,1,1] [10,4] := by
  exact rowSquare_join (by decide) sg29 sg429

lemma sg2539 : RowSquare [4,3,2,1,1,1,1,1] [11,3] := by
  exact rowSquare_join (by decide) sg80 sg235

lemma sg2540 : RowSquare [4,3,2,1,1,1,1,1] [12,2] := by
  exact rowSquare_join (by decide) sg81 sg235

lemma sg2541 : RowSquare [4,3,2,1,1,1,1,1] [13,1] := by
  exact rowSquare_join (by decide) sg82 sg235

lemma sg2542 : RowSquare [4,3,2,2,1,1,1] [5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg849

lemma sg2543 : RowSquare [4,3,2,2,2,1] [5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg849

lemma sg2544 : RowSquare [4,3,2,2,2,1] [6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg850

lemma sg2545 : RowSquare [4,3,3,2,1,1] [2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1232

lemma sg2546 : RowSquare [4,4,1,1,1,1,1,1] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg178 sg178

lemma sg2547 : RowSquare [4,4,1,1,1,1,1,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg179

lemma sg2548 : RowSquare [4,4,1,1,1,1,1,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg180

lemma sg2549 : RowSquare [4,4,1,1,1,1,1,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg181

lemma sg2550 : RowSquare [4,4,1,1,1,1,1,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg179 sg179

lemma sg2551 : RowSquare [4,4,1,1,1,1,1,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg179 sg180

lemma sg2552 : RowSquare [4,4,1,1,1,1,1,1] [4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg179 sg181

lemma sg2553 : RowSquare [4,4,1,1,1,1,1,1] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg66 sg372

lemma sg2554 : RowSquare [4,4,1,1,1,1,1,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg66 sg373

lemma sg2555 : RowSquare [4,4,1,1,1,1,1,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg185

lemma sg2556 : RowSquare [4,4,1,1,1,1,1,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg67 sg371

lemma sg2557 : RowSquare [4,4,1,1,1,1,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg180 sg180

lemma sg2558 : RowSquare [4,4,1,1,1,1,1,1] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg371

lemma sg2559 : RowSquare [4,4,1,1,1,1,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg67 sg373

lemma sg2560 : RowSquare [4,4,1,1,1,1,1,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg68 sg372

lemma sg2561 : RowSquare [4,4,1,1,1,1,1,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg181 sg181

lemma sg2562 : RowSquare [4,4,1,1,1,1,1,1] [5,3,3,3] := by
  exact rowSquare_join (by decide) sg69 sg373

lemma sg2563 : RowSquare [4,4,1,1,1,1,1,1] [5,5,4] := by
  exact rowSquare_join (by decide) sg68 sg378

lemma sg2564 : RowSquare [4,4,1,1,1,1,1,1] [6,3,3,2] := by
  exact rowSquare_join (by decide) sg181 sg186

lemma sg2565 : RowSquare [4,4,1,1,1,1,1,1] [7,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg721

lemma sg2566 : RowSquare [4,4,1,1,1,1,1,1] [7,7] := by
  exact rowSquare_join (by decide) sg71 sg383

lemma sg2567 : RowSquare [4,4,1,1,1,1,1,1] [8,2,2,2] := by
  exact rowSquare_join (by decide) sg13 sg723

lemma sg2568 : RowSquare [4,4,1,1,1,1,1,1] [8,6] := by
  exact rowSquare_join (by decide) sg14 sg722

lemma sg2569 : RowSquare [4,4,1,1,1,1,1,1] [9,5] := by
  exact rowSquare_join (by decide) sg14 sg724

lemma sg2570 : RowSquare [4,4,1,1,1,1,1,1] [10,4] := by
  exact rowSquare_join (by decide) sg14 sg725

lemma sg2571 : RowSquare [4,4,1,1,1,1,1,1] [12,2] := by
  exact rowSquare_join (by decide) sg85 sg235

lemma sg2572 : RowSquare [4,4,1,1,1,1,1,1] [13,1] := by
  exact rowSquare_join (by decide) sg15 sg726

lemma sg2574 : RowSquare [4,4,2,2,1,1] [4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1651

lemma sg2575 : RowSquare [5,1,1,1,1,1,1,1,1,1] [8,4,2] := by
  exact rowSquare_join (by decide) sg20 sg1016

lemma sg2576 : RowSquare [5,3,1,1,1,1,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg586

lemma sg2577 : RowSquare [5,3,1,1,1,1,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg586

lemma sg2578 : RowSquare [5,3,1,1,1,1,1,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg587

lemma sg2579 : RowSquare [5,3,1,1,1,1,1,1] [3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg586

lemma sg2580 : RowSquare [5,3,1,1,1,1,1,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg588

lemma sg2581 : RowSquare [5,3,1,1,1,1,1,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg589

lemma sg2582 : RowSquare [5,3,1,1,1,1,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg590

lemma sg2583 : RowSquare [5,3,1,1,1,1,1,1] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg35 sg586

lemma sg2584 : RowSquare [5,3,1,1,1,1,1,1] [4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg33 sg587

lemma sg2585 : RowSquare [5,3,1,1,1,1,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg36 sg586

lemma sg2586 : RowSquare [5,3,1,1,1,1,1,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg998

lemma sg2587 : RowSquare [5,3,1,1,1,1,1,1] [5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg37 sg586

lemma sg2588 : RowSquare [5,3,2,1,1,1,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg2074

lemma sg2589 : RowSquare [5,3,2,1,1,1,1] [3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg313

lemma sg2590 : RowSquare [5,3,2,1,1,1,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2075

lemma sg2591 : RowSquare [5,3,2,2,1,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg1687

lemma sg2592 : RowSquare [5,4,1,1,1,1,1] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg22 sg586

lemma sg2593 : RowSquare [5,4,1,1,1,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg586

lemma sg2594 : RowSquare [5,4,1,1,1,1,1] [5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg586

lemma sg2595 : RowSquare [5,4,1,1,1,1,1] [7,7] := by
  exact rowSquare_join (by decide) sg14 sg748

lemma sg2597 : RowSquare [5,4,2,2,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg153 sg122

lemma sg2598 : RowSquare [5,4,2,2,1] [2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg152 sg122

lemma sg2599 : RowSquare [5,4,2,2,1] [2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg151 sg122

lemma sg2600 : RowSquare [5,4,2,2,1] [2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg151 sg121

lemma sg2601 : RowSquare [5,4,2,2,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg151 sg120

lemma sg2602 : RowSquare [5,4,2,2,1] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg14 sg761

lemma sg2603 : RowSquare [5,4,2,2,1] [3,2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg150 sg122

lemma sg2604 : RowSquare [5,4,2,2,1] [3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg148 sg122

lemma sg2605 : RowSquare [5,4,2,2,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg148 sg120

lemma sg2606 : RowSquare [5,4,2,2,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg148 sg118

lemma sg2607 : RowSquare [5,4,2,2,1] [3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg147 sg122

lemma sg2608 : RowSquare [5,4,2,2,1] [3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg147 sg121

lemma sg2609 : RowSquare [5,4,2,2,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg147 sg118

lemma sg2610 : RowSquare [5,4,2,2,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2106

lemma sg2611 : RowSquare [5,4,2,2,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg144 sg122

lemma sg2612 : RowSquare [5,4,2,2,1] [7,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg21 sg561

lemma sg2613 : RowSquare [5,4,2,2,1] [7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg21 sg562

lemma sg2614 : RowSquare [5,4,3,2] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2110

lemma sg2615 : RowSquare [5,4,3,2] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg2111

lemma sg2616 : RowSquare [5,4,3,2] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1181

lemma sg2617 : RowSquare [5,4,3,2] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2113

lemma sg2618 : RowSquare [6,1,1,1,1,1,1,1,1] [8,5,1] := by
  exact rowSquare_join (by decide) sg7 sg1358

lemma sg2619 : RowSquare [6,2,1,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1327

lemma sg2620 : RowSquare [6,2,1,1,1,1,1,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg1332

lemma sg2621 : RowSquare [6,2,1,1,1,1,1,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg1332

lemma sg2622 : RowSquare [6,2,2,1,1,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg891

lemma sg2623 : RowSquare [6,2,2,1,1,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg892

lemma sg2624 : RowSquare [6,2,2,2,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg809

lemma sg2625 : RowSquare [6,3,1,1,1,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg10 sg892

lemma sg2627 : RowSquare [6,3,2,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg205 sg113

lemma sg2628 : RowSquare [6,3,2,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg204 sg113

lemma sg2629 : RowSquare [6,3,2,1,1,1] [2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg202 sg113

lemma sg2630 : RowSquare [6,3,2,1,1,1] [2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg202 sg112

lemma sg2631 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg202 sg111

lemma sg2632 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg92 sg244

lemma sg2633 : RowSquare [6,3,2,1,1,1] [2,2,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg92 sg241

lemma sg2634 : RowSquare [6,3,2,1,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg199 sg112

lemma sg2635 : RowSquare [6,3,2,1,1,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg199 sg111

lemma sg2636 : RowSquare [6,3,2,1,1,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg91 sg241

lemma sg2637 : RowSquare [6,3,2,1,1,1] [3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg198 sg113

lemma sg2638 : RowSquare [6,3,2,1,1,1] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg198 sg111

lemma sg2639 : RowSquare [6,3,2,1,1,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg89 sg244

lemma sg2640 : RowSquare [6,3,2,1,1,1] [3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg89 sg241

lemma sg2641 : RowSquare [6,3,2,1,1,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg89 sg240

lemma sg2642 : RowSquare [6,3,2,1,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg89 sg239

lemma sg2643 : RowSquare [6,3,2,1,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg34 sg459

lemma sg2644 : RowSquare [6,3,2,1,1,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2135

lemma sg2645 : RowSquare [6,3,3,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2139

lemma sg2646 : RowSquare [6,3,3,1,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2140

lemma sg2647 : RowSquare [6,3,3,1,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg2141

lemma sg2648 : RowSquare [6,3,3,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg476

lemma sg2649 : RowSquare [6,3,3,1,1] [4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2142

lemma sg2650 : RowSquare [6,3,3,1,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2143

lemma sg2651 : RowSquare [6,3,3,1,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg0 sg2144

lemma sg2652 : RowSquare [6,3,3,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2145

lemma sg2653 : RowSquare [6,3,3,1,1] [4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg826

lemma sg2654 : RowSquare [6,3,3,1,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg826

lemma sg2655 : RowSquare [6,3,3,1,1] [5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1648

lemma sg2656 : RowSquare [6,3,3,2] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg481

lemma sg2657 : RowSquare [6,3,3,2] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg483

lemma sg2658 : RowSquare [6,3,3,2] [5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg22 sg548

lemma sg2659 : RowSquare [6,3,3,2] [5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg548

lemma sg2660 : RowSquare [6,3,3,2] [6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg1181

lemma sg2661 : RowSquare [6,4,2,2] [5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg56 sg331

lemma sg2662 : RowSquare [6,4,3,1] [2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1232

lemma sg2663 : RowSquare [6,4,3,1] [3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1233

lemma sg2664 : RowSquare [6,4,4] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg516

lemma sg2665 : RowSquare [6,5,2,1] [2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg849

lemma sg2666 : RowSquare [6,5,2,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg850

lemma sg2667 : RowSquare [6,5,2,1] [3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg849

lemma sg2668 : RowSquare [6,5,2,1] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg851

lemma sg2669 : RowSquare [6,5,2,1] [3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg295

lemma sg2670 : RowSquare [6,5,2,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg852

lemma sg2671 : RowSquare [6,5,2,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg296

lemma sg2672 : RowSquare [6,5,2,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg297

lemma sg2673 : RowSquare [6,5,2,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg854

lemma sg2674 : RowSquare [6,5,2,1] [4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg510

lemma sg2675 : RowSquare [6,5,2,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg165 sg142

lemma sg2676 : RowSquare [6,5,2,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg850

lemma sg2677 : RowSquare [6,5,2,1] [4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg510

lemma sg2678 : RowSquare [6,5,2,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg9 sg877

lemma sg2679 : RowSquare [6,5,2,1] [4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg165 sg144

lemma sg2680 : RowSquare [6,5,2,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg851

lemma sg2681 : RowSquare [6,5,2,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg511

lemma sg2682 : RowSquare [6,5,2,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg300

lemma sg2683 : RowSquare [6,5,2,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg166 sg143

lemma sg2684 : RowSquare [6,5,2,1] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg301

lemma sg2685 : RowSquare [6,5,2,1] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg166 sg144

lemma sg2686 : RowSquare [6,5,2,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg76 sg297

lemma sg2687 : RowSquare [6,5,2,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg83 sg286

lemma sg2688 : RowSquare [6,5,2,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg207 sg123

lemma sg2689 : RowSquare [6,5,2,1] [5,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg15 sg849

lemma sg2690 : RowSquare [6,5,3] [2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg306

lemma sg2691 : RowSquare [6,5,3] [3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg308

lemma sg2692 : RowSquare [6,5,3] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg309

lemma sg2693 : RowSquare [6,6,1,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg877

lemma sg2694 : RowSquare [6,6,1,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg13 sg883

lemma sg2695 : RowSquare [6,6,1,1] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg13 sg885

lemma sg2696 : RowSquare [6,6,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg886

lemma sg2697 : RowSquare [6,6,1,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg83 sg296

lemma sg2698 : RowSquare [6,6,1,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg83 sg297

lemma sg2699 : RowSquare [7,1,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2251

lemma sg2700 : RowSquare [7,1,1,1,1,1,1,1] [3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2252

lemma sg2701 : RowSquare [7,1,1,1,1,1,1,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2256

lemma sg2703 : RowSquare [7,2,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg233 sg109

lemma sg2704 : RowSquare [7,2,1,1,1,1,1] [2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg232 sg109

lemma sg2705 : RowSquare [7,2,1,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg237

lemma sg2706 : RowSquare [7,2,1,1,1,1,1] [2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg105 sg236

lemma sg2707 : RowSquare [7,2,1,1,1,1,1] [2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg451

lemma sg2708 : RowSquare [7,2,1,1,1,1,1] [2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg806

lemma sg2709 : RowSquare [7,2,1,1,1,1,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg806

lemma sg2710 : RowSquare [7,2,1,1,1,1,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg1256

lemma sg2711 : RowSquare [7,2,1,1,1,1,1] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg46 sg449

lemma sg2712 : RowSquare [7,2,1,1,1,1,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg804

lemma sg2713 : RowSquare [7,2,1,1,1,1,1] [3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg449

lemma sg2714 : RowSquare [7,2,1,1,1,1,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg1254

lemma sg2715 : RowSquare [7,2,1,1,1,1,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg1253

lemma sg2716 : RowSquare [7,2,1,1,1,1,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg801

lemma sg2717 : RowSquare [7,2,2,2,1] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg22 sg586

lemma sg2718 : RowSquare [7,2,2,2,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg23 sg586

lemma sg2719 : RowSquare [7,2,2,2,1] [5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg24 sg586

lemma sg2720 : RowSquare [7,3,1,1,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg888

lemma sg2721 : RowSquare [7,3,1,1,1,1] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg889

lemma sg2722 : RowSquare [7,3,1,1,1,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg890

lemma sg2723 : RowSquare [7,3,1,1,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg891

lemma sg2724 : RowSquare [7,3,1,1,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg892

lemma sg2725 : RowSquare [7,3,1,1,1,1] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1258

lemma sg2726 : RowSquare [7,3,1,1,1,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg1758

lemma sg2727 : RowSquare [7,3,1,1,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg888

lemma sg2728 : RowSquare [7,3,1,1,1,1] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg894

lemma sg2729 : RowSquare [7,3,1,1,1,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg807

lemma sg2730 : RowSquare [7,3,1,1,1,1] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg16 sg809

lemma sg2731 : RowSquare [7,3,1,1,1,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg889

lemma sg2732 : RowSquare [7,3,1,1,1,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg807

lemma sg2733 : RowSquare [7,3,1,1,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg809

lemma sg2734 : RowSquare [7,3,1,1,1,1] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1261

lemma sg2735 : RowSquare [7,3,1,1,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg899

lemma sg2736 : RowSquare [7,3,1,1,1,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1262

lemma sg2737 : RowSquare [7,3,1,1,1,1] [5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg1 sg1762

lemma sg2738 : RowSquare [7,3,1,1,1,1] [5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg18 sg809

lemma sg2739 : RowSquare [7,3,1,1,1,1] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg814

lemma sg2740 : RowSquare [7,3,1,1,1,1] [6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg521

lemma sg2741 : RowSquare [7,3,2,1,1] [3,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg26 sg586

lemma sg2742 : RowSquare [7,3,2,1,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg32 sg534

lemma sg2743 : RowSquare [7,3,2,1,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg312

lemma sg2744 : RowSquare [7,3,2,1,1] [3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg27 sg586

lemma sg2745 : RowSquare [7,3,2,1,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg535

lemma sg2746 : RowSquare [7,3,2,1,1] [3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg313

lemma sg2747 : RowSquare [7,3,2,1,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg314

lemma sg2748 : RowSquare [7,3,2,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg315

lemma sg2749 : RowSquare [7,3,2,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg537

lemma sg2750 : RowSquare [7,3,2,1,1] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg28 sg586

lemma sg2751 : RowSquare [7,3,2,1,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg75 sg312

lemma sg2752 : RowSquare [7,3,2,1,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg316

lemma sg2753 : RowSquare [7,3,2,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg29 sg586

lemma sg2754 : RowSquare [7,3,2,1,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg317

lemma sg2755 : RowSquare [7,3,2,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg32 sg541

lemma sg2756 : RowSquare [7,3,2,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg271

lemma sg2757 : RowSquare [7,3,2,1,1] [5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg30 sg586

lemma sg2758 : RowSquare [7,3,2,1,1] [6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg31 sg586

lemma sg2759 : RowSquare [7,3,2,2] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg66 sg330

lemma sg2760 : RowSquare [7,3,2,2] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg67 sg330

lemma sg2761 : RowSquare [7,3,2,2] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg143

lemma sg2762 : RowSquare [7,3,2,2] [3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg330

lemma sg2763 : RowSquare [7,3,2,2] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg144

lemma sg2764 : RowSquare [7,3,2,2] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg66 sg334

lemma sg2765 : RowSquare [7,3,2,2] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg71 sg330

lemma sg2766 : RowSquare [7,3,2,2] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg180 sg143

lemma sg2767 : RowSquare [7,3,2,2] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg67 sg334

lemma sg2768 : RowSquare [7,3,2,2] [5,4,2,2,1] := by
  exact rowSquare_join (by decide) sg180 sg146

lemma sg2769 : RowSquare [7,3,3,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg154

lemma sg2770 : RowSquare [7,3,3,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg155

lemma sg2771 : RowSquare [7,3,3,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg156

lemma sg2772 : RowSquare [7,3,3,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg550

lemma sg2773 : RowSquare [7,3,3,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg551

lemma sg2774 : RowSquare [7,3,3,1] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg154 sg179

lemma sg2775 : RowSquare [7,3,3,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg154 sg180

lemma sg2776 : RowSquare [7,3,3,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg10 sg940

lemma sg2777 : RowSquare [7,3,3,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg155 sg180

lemma sg2778 : RowSquare [7,3,3,1] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg285

lemma sg2779 : RowSquare [7,3,3,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg287

lemma sg2780 : RowSquare [7,3,3,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg89 sg286

lemma sg2781 : RowSquare [7,3,3,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg156 sg181

lemma sg2782 : RowSquare [7,3,3,1] [5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg154 sg184

lemma sg2783 : RowSquare [7,4,1,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg914

lemma sg2784 : RowSquare [7,4,1,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg915

lemma sg2785 : RowSquare [7,4,1,1,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14 sg911

lemma sg2786 : RowSquare [7,4,1,1,1] [4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg534

lemma sg2787 : RowSquare [7,4,1,1,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg312

lemma sg2788 : RowSquare [7,4,1,1,1] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg16 sg841

lemma sg2789 : RowSquare [7,4,1,1,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg39 sg537

lemma sg2790 : RowSquare [7,4,1,1,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg838

lemma sg2791 : RowSquare [7,4,1,1,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg535

lemma sg2792 : RowSquare [7,4,1,1,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg920

lemma sg2793 : RowSquare [7,4,1,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg841

lemma sg2794 : RowSquare [7,4,1,1,1] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg313

lemma sg2795 : RowSquare [7,4,1,1,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg13 sg922

lemma sg2796 : RowSquare [7,4,1,1,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg97 sg270

lemma sg2797 : RowSquare [7,4,1,1,1] [5,5,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg846

lemma sg2798 : RowSquare [7,4,2,1] [2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg74 sg330

lemma sg2799 : RowSquare [7,4,2,1] [3,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg178 sg165

lemma sg2800 : RowSquare [7,4,2,1] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg76 sg330

lemma sg2801 : RowSquare [7,4,2,1] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg166

lemma sg2802 : RowSquare [7,4,2,1] [3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg332

lemma sg2803 : RowSquare [7,4,2,1] [3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg77 sg330

lemma sg2804 : RowSquare [7,4,2,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg167

lemma sg2805 : RowSquare [7,4,2,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg74 sg333

lemma sg2806 : RowSquare [7,4,2,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg334

lemma sg2807 : RowSquare [7,4,2,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg564

lemma sg2808 : RowSquare [7,4,2,1] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg850

lemma sg2809 : RowSquare [7,4,2,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg178 sg168

lemma sg2810 : RowSquare [7,4,2,1] [4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg850

lemma sg2811 : RowSquare [7,4,2,1] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg169

lemma sg2812 : RowSquare [7,4,2,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg170

lemma sg2813 : RowSquare [7,4,2,1] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg87 sg296

lemma sg2814 : RowSquare [7,4,2,1] [4,3,3,3,1] := by
  exact rowSquare_join (by decide) sg87 sg297

lemma sg2815 : RowSquare [7,4,2,1] [4,4,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg80 sg330

lemma sg2816 : RowSquare [7,4,2,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg171

lemma sg2817 : RowSquare [7,4,2,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg143

lemma sg2818 : RowSquare [7,4,2,1] [4,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg74 sg339

lemma sg2819 : RowSquare [7,4,2,1] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg194 sg144

lemma sg2820 : RowSquare [7,4,2,1] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg297

lemma sg2821 : RowSquare [7,4,2,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg97 sg286

lemma sg2822 : RowSquare [7,4,2,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg195 sg144

lemma sg2823 : RowSquare [7,4,2,1] [5,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg18 sg850

lemma sg2824 : RowSquare [7,4,2,1] [5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg172

lemma sg2825 : RowSquare [7,4,2,1] [5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg173

lemma sg2826 : RowSquare [7,4,2,1] [5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg145

lemma sg2827 : RowSquare [7,4,2,1] [5,3,3,3] := by
  exact rowSquare_join (by decide) sg98 sg287

lemma sg2828 : RowSquare [7,4,2,1] [5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg174

lemma sg2829 : RowSquare [7,4,2,1] [5,4,3,2] := by
  exact rowSquare_join (by decide) sg195 sg146

lemma sg2830 : RowSquare [7,4,2,1] [5,5,2,2] := by
  exact rowSquare_join (by decide) sg88 sg300

lemma sg2831 : RowSquare [7,4,2,1] [6,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19 sg850

lemma sg2832 : RowSquare [7,4,2,1] [6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg175

lemma sg2833 : RowSquare [7,4,2,1] [6,2,2,2,2] := by
  exact rowSquare_join (by decide) sg196 sg145

lemma sg2834 : RowSquare [7,4,2,1] [6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg176

lemma sg2835 : RowSquare [7,4,2,1] [6,6,1,1] := by
  exact rowSquare_join (by decide) sg88 sg302

lemma sg2836 : RowSquare [7,4,2,1] [7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg178 sg177

lemma sg2837 : RowSquare [7,4,3] [3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg32 sg577

lemma sg2838 : RowSquare [7,4,3] [3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg74 sg348

lemma sg2839 : RowSquare [7,4,3] [3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg306

lemma sg2840 : RowSquare [7,4,3] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg74 sg350

lemma sg2841 : RowSquare [7,4,3] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg32 sg578

lemma sg2842 : RowSquare [7,4,3] [4,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg45 sg516

lemma sg2843 : RowSquare [7,4,3] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg87 sg307

lemma sg2844 : RowSquare [7,4,3] [4,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg193 sg154

lemma sg2845 : RowSquare [7,4,3] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg88 sg307

lemma sg2846 : RowSquare [7,4,3] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg155

lemma sg2847 : RowSquare [7,4,3] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg89 sg307

lemma sg2848 : RowSquare [7,4,3] [4,3,3,2,2] := by
  exact rowSquare_join (by decide) sg87 sg309

lemma sg2849 : RowSquare [7,4,3] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg34 sg577

lemma sg2850 : RowSquare [7,4,3] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg155

lemma sg2851 : RowSquare [7,4,3] [4,4,3,2,1] := by
  exact rowSquare_join (by decide) sg194 sg156

lemma sg2852 : RowSquare [7,4,3] [4,4,3,3] := by
  exact rowSquare_join (by decide) sg88 sg310

lemma sg2853 : RowSquare [7,4,3] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg89 sg309

lemma sg2854 : RowSquare [7,4,3] [5,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg90 sg307

lemma sg2855 : RowSquare [7,4,3] [5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg193 sg157

lemma sg2856 : RowSquare [7,4,3] [5,3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg91 sg307

lemma sg2857 : RowSquare [7,4,3] [5,3,2,2,2] := by
  exact rowSquare_join (by decide) sg194 sg157

lemma sg2858 : RowSquare [7,4,3] [5,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg159

lemma sg2859 : RowSquare [7,4,3] [5,3,3,3] := by
  exact rowSquare_join (by decide) sg90 sg310

lemma sg2860 : RowSquare [7,4,3] [5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg92 sg307

lemma sg2861 : RowSquare [7,4,3] [5,4,3,1,1] := by
  exact rowSquare_join (by decide) sg194 sg159

lemma sg2862 : RowSquare [7,4,3] [6,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg93 sg307

lemma sg2863 : RowSquare [7,4,3] [6,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg94 sg307

lemma sg2864 : RowSquare [7,4,3] [6,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg193 sg162

lemma sg2865 : RowSquare [7,4,3] [6,3,3,1,1] := by
  exact rowSquare_join (by decide) sg196 sg159

lemma sg2866 : RowSquare [7,4,3] [7,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg95 sg307

lemma sg2867 : RowSquare [7,5,1,1] [3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg958

lemma sg2868 : RowSquare [7,5,1,1] [3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg330

lemma sg2869 : RowSquare [7,5,1,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg13 sg959

lemma sg2870 : RowSquare [7,5,1,1] [3,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg960

lemma sg2871 : RowSquare [7,5,1,1] [3,3,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg961

lemma sg2872 : RowSquare [7,5,1,1] [4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg84 sg330

lemma sg2873 : RowSquare [7,5,1,1] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg39 sg562

lemma sg2874 : RowSquare [7,5,1,1] [4,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg83 sg331

lemma sg2875 : RowSquare [7,5,1,1] [4,3,3,2,1,1] := by
  exact rowSquare_join (by decide) sg142 sg207

lemma sg2876 : RowSquare [7,5,1,1] [4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg40 sg562

lemma sg2877 : RowSquare [7,6,1] [4,4,4,1,1] := by
  exact rowSquare_join (by decide) sg83 sg357

lemma sg2878 : RowSquare [7,6,1] [4,4,4,2] := by
  exact rowSquare_join (by decide) sg207 sg167

lemma sg2879 : RowSquare [8,1,1,1,1,1,1] [2,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2251

lemma sg2880 : RowSquare [8,1,1,1,1,1,1] [3,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2252

lemma sg2881 : RowSquare [8,1,1,1,1,1,1] [3,2,2,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2256

lemma sg2882 : RowSquare [8,1,1,1,1,1,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2260

lemma sg2883 : RowSquare [8,1,1,1,1,1,1] [4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2262

lemma sg2884 : RowSquare [8,1,1,1,1,1,1] [4,3,2,2,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2263

lemma sg2885 : RowSquare [8,1,1,1,1,1,1] [5,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2264

lemma sg2886 : RowSquare [8,1,1,1,1,1,1] [5,4,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg2267

lemma sg2887 : RowSquare [8,2,1,1,1,1] [2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1327

lemma sg2888 : RowSquare [8,2,1,1,1,1] [3,3,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1329

lemma sg2889 : RowSquare [8,2,1,1,1,1] [3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1330

lemma sg2890 : RowSquare [8,2,1,1,1,1] [3,3,3,2,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg1331

lemma sg2891 : RowSquare [8,2,1,1,1,1] [3,3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg4 sg1332

lemma sg2892 : RowSquare [8,2,1,1,1,1] [4,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg2 sg1758

lemma sg2893 : RowSquare [8,2,1,1,1,1] [4,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg5 sg1332

lemma sg2894 : RowSquare [8,2,1,1,1,1] [4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg17 sg891

lemma sg2895 : RowSquare [8,2,1,1,1,1] [4,4,2,2,2] := by
  exact rowSquare_join (by decide) sg17 sg892

lemma sg2896 : RowSquare [8,2,1,1,1,1] [5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg893

end UniversalTensorSquare
end
end

end OAI
